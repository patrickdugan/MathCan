"""AHR-QPU-03B/C and 04: read-only Kingston diagnostics and ideal design checks.

Run from any working directory. Reads the pinned parent study receipts. No IBM SDK,
credentials, hardware requests, or submission entry points.
"""
import json
import math
import sys
from dataclasses import replace
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
PARENT = ROOT.parent / "ibm_qpu_03"
sys.path.insert(0, str(PARENT))
from controls import CENTER
from plaquette_estimator import probability, settings, Setting
from q3_hamiltonian import BIANCHI, CHORD_COLUMNS, D1, EDGE_INDEX, FACES, chord_field, face_flux, wrap

PAIRS = ((2, 3), (2, 5), (3, 5))
SEED = 20261124


def read(relative):
    return json.loads((PARENT / relative).read_text(encoding="utf-8"))


def hardware_diagnostics():
    h = read("receipts/hardware/hardware_counts.json")
    a = read("receipts/hardware/hardware_analysis.json")
    m = read("receipts/execution_refresh/q3_candidate_manifest.json")
    ids = [r["case_id"] for r in m["settings"]]
    assert list(h["counts"]) == ids and len(set(ids)) == 48
    rows = []
    for r in a["cases"]:
        counts = h["counts"][r["case_id"]]
        assert sum(counts.values()) == r["shots"] == 4096
        assert counts.get(format(r["setting"]["start"], "03b"), 0) == r["return_count"]
        assert abs(r["observed"] - r["return_count"]/r["shots"]) < 1e-12
        rows.append(r)
    signal = [r for r in rows if r["role"] == "signal"]
    sig = sorted([r for r in signal if r["setting"]["face"] == 0],
                 key=lambda r: r["setting"]["offset_index"])
    copy = sorted([r for r in rows if r["role"] == "gauge_copy"],
                  key=lambda r: r["setting"]["offset_index"])
    assert len(rows) == 48 and len(signal) == 24 and len(sig) == len(copy) == 4
    comparisons = []
    for s, g in zip(sig, copy, strict=True):
        assert s["setting"] == g["setting"]
        assert abs(s["exact"] - g["exact"]) < 1e-12
        assert s["classical_bit_to_physical"] == g["classical_bit_to_physical"]
        raw = g["observed"] - s["observed"]
        delta_aer = g["aer"] - s["aer"]
        var = (g["aer"]*(1-g["aer"])+s["aer"]*(1-s["aer"]))/s["shots"]
        comparisons.append({"quadrant": s["setting"]["offset_index"], "raw": raw,
                            "aer_delta": delta_aer, "adjusted": raw-delta_aer,
                            "shot_noise_sd": math.sqrt(var), "z": (raw-delta_aer)/math.sqrt(var),
                            "two_qubit_gates": [s["two_qubit_gates"], g["two_qubit_gates"]],
                            "depth": [s["depth"], g["depth"]]})
    chi = sum(r["z"]**2 for r in comparisons)
    mse = np.mean([(r["observed"]-r["aer"])**2 for r in signal])
    variance = np.mean([r["aer"]*(1-r["aer"])/r["shots"] for r in signal])
    joint = a["likelihood"]["expected_field_local_joint_chi_square"]
    return {"job": a["job_id"], "shots": sum(r["shots"] for r in rows),
            "gauge_pairs": comparisons, "conditional_shot_only_chi_square4": chi,
            "conditional_nominal_tail": math.exp(-chi/2)*(1+chi/2),
            "signal_rmse": float(np.sqrt(mse)), "shot_only_rms": float(np.sqrt(variance)),
            "excess_residual_rms_diagnostic": float(np.sqrt(max(0,mse-variance))),
            "joint_chord_score": joint, "posthoc_variance_inflation_to_boundary": joint/11.070497693516351,
            "warning": "Exploratory; fixed Aer model and independent counting only. Shared hardware noise and circuit-dependent synthesis are not separated. This is not a channel-process covariance measurement."}


def intact_consistency():
    """One extra probe-specific closure-like coordinate, not an impossible static flux."""
    a = read("receipts/hardware/hardware_analysis.json")
    st = read("receipts/live/statistics.json")["designs"]["likelihood"]
    m = read("receipts/execution_refresh/q3_candidate_manifest.json")
    cases = settings([m["likelihood_time"]])
    rows = sorted([r for r in a["cases"] if r["role"] == "signal"],
                  key=lambda r: (r["setting"]["face"], r["setting"]["offset_index"]))
    assert [r["case_id"] for r in rows] == ["signal/"+c.id for c in cases]
    intercept, contrast = np.array(st["transfer_intercept"]), np.array(st["transfer_contrast"])
    shared = np.asarray(st["nominal_shared_covariance_rad_free_p"])
    shots = np.array([r["shots"] for r in rows])
    observed = np.array([r["observed"] for r in rows])

    def model(x):
        q = x[5]
        displaced = [replace(c, offset=c.offset+q*BIANCHI[c.face]/6) for c in cases]
        return np.clip(intercept+contrast*probability(chord_field(x[:5]), displaced), .001, .999)

    x0 = np.r_[CENTER,0.]
    p = model(x0)
    h = 1e-5
    jac = np.column_stack([(model(x0+h*e)-model(x0-h*e))/(2*h) for e in np.eye(6)])
    cov = np.diag(p*(1-p)/shots)+(shared+shared.T)/2
    L = np.linalg.cholesky(cov)
    design = np.linalg.solve(L,jac)
    residual = np.linalg.solve(L,observed-p)
    assert np.linalg.matrix_rank(design[:,:5]) == 5 and np.linalg.matrix_rank(design) == 6
    estimate = np.linalg.lstsq(design,residual,rcond=None)[0]
    cov6 = np.linalg.inv(design.T@design)
    sd = np.sqrt(cov6[-1,-1])
    base_fit = np.linalg.lstsq(design[:,:5],residual,rcond=None)[0]
    base_r = residual-design[:,:5]@base_fit
    ext_r = residual-design@estimate
    # Plant an exactly linear local perturbation and check identifiability.
    planted = np.array([.01,-.02,.015,0.,-.01,.08])
    np.testing.assert_allclose(np.linalg.lstsq(design,design@planted,rcond=None)[0],planted,atol=1e-10)
    return {"rank_static": 5,"rank_with_probe_displacement": 6,
            "q_hat_degrees": float(np.degrees(estimate[-1])),
            "q_local_sd_degrees": float(np.degrees(sd)),
            "q_local_95_halfwidth_degrees": float(np.degrees(1.96*sd)),
            "conditional_q_z": float(estimate[-1]/sd),
            "static_whitened_residual_squared": float(base_r@base_r),
            "extended_whitened_residual_squared": float(ext_r@ext_r),
            "conditional_delta_chi_square": float(base_r@base_r-ext_r@ext_r),
            "warning": "Posthoc local linearization at commanded field under frozen transfer covariance. q is a setting-dependent displacement along b/6, not a physical violation of cubical Bianchi. Requires holdout and refreshed calibration."}


def square_scan(pair,t,theta):
    theta=np.asarray(theta)
    a,b=np.log(pair)
    angles=theta[...,None]+np.arange(4)*np.pi/2
    H=np.broadcast_to(np.diag([0,a,b,a+b]).astype(complex),angles.shape+(4,4)).copy()
    for i,j in ((0,1),(0,2),(2,3)):
        H[...,i,j]=H[...,j,i]=1
    H[...,1,3]=np.exp(1j*angles); H[...,3,1]=H[...,1,3].conj()
    v,u=np.linalg.eigh(H)
    return abs(np.sum(abs(u[...,0,:])**2*np.exp(-1j*t*v),axis=-1))**2


def z(p):
    return ((p[...,0]-p[...,2])+1j*(p[...,3]-p[...,1]))/2


def phase_var(p,n):
    q=z(p); v=p*(1-p)/n
    return (q.imag**2*(v[...,0]+v[...,2])+q.real**2*(v[...,1]+v[...,3]))/(4*np.maximum(abs(q)**4,1e-24))


def optimize(pair,n=2048):
    train=np.linspace(-np.pi,np.pi,65,endpoint=False)
    rows=[]
    for t in np.arange(.5,2.501,.025):
        p=square_scan(pair,t,train); ref=square_scan(pair,t,0.)
        if min(np.min(abs(z(p))),abs(z(ref)))<.04:
            continue
        bias=wrap(np.angle(z(p)*z(ref).conj())-train)
        var=phase_var(p,n)+phase_var(ref,n)
        rows.append((float(np.max(bias*bias+var)),float(t),float(np.max(abs(bias))),
                     float(np.min(abs(z(p)))),float(np.max(np.sqrt(var)))))
    return min(rows)


def masked_design():
    """Isolated face experiments with independent reference counts; no enforced closure."""
    opts=[optimize(pair) for pair in PAIRS]
    field=chord_field(CENTER)
    D=D1[:,CHORD_COLUMNS]
    assert not np.any(BIANCHI@D)
    # Verify the two-qubit canonical square against the actual masked 8-site graph.
    for f,(i,j,u) in enumerate(FACES):
        edge=EDGE_INDEX[tuple(sorted((u^(1<<i),u^(1<<i)^(1<<j))))]
        t=opts[f//2][1]
        scan=[Setting(f,u,edge,1,float(k*np.pi/2),t,k,4) for k in range(4)]
        mask=np.abs(D1[f])
        np.testing.assert_allclose(probability(field,scan,mask),
            square_scan(PAIRS[f//2],t,face_flux(field)[f]),atol=2e-13,rtol=0)
    rng=np.random.default_rng(SEED)
    truth=wrap((CENTER+rng.uniform(-.19,.19,(2000,5)))@D.T)
    assert np.max(abs(wrap(truth@BIANCHI)))<1e-12
    receipts=[]
    for n in (2048,4096):
        obs=[]; var=[]; bias=[]
        for f in range(6):
            pair=PAIRS[f//2]; t=opts[f//2][1]
            p=square_scan(pair,t,truth[:,f]); ref=square_scan(pair,t,np.zeros(len(truth)))
            ph=rng.binomial(n,p)/n; rh=rng.binomial(n,ref)/n
            obs.append(np.angle(z(ph)*z(rh).conj()))
            var.append(phase_var((ph*n+.5)/(n+1),n)+phase_var((rh*n+.5)/(n+1),n))
            bias.append(wrap(np.angle(z(p)*z(ref).conj())-truth[:,f]))
        est=np.array(obs).T; v=np.array(var).T
        err=wrap(est-truth); closure=wrap(est@BIANCHI); sigma=np.sqrt(v.sum(axis=1))
        receipts.append({"shots_per_setting":n,"primary_circuits":48,"primary_shots":48*n,
            "worst_face_rmse_deg":float(np.max(np.degrees(np.sqrt((err**2).mean(axis=0))))),
            "closure_rmse_deg":float(np.degrees(np.sqrt(np.mean(closure**2)))),
            "median_closure_95_halfwidth_deg":float(np.degrees(np.median(1.96*sigma))),
            "closure_coverage":float(np.mean(abs(closure)<=1.96*sigma)),
            "max_noiseless_alias_deg":float(np.degrees(np.max(np.abs(bias))))})
    assert all(r["closure_coverage"]>.90 and r["worst_face_rmse_deg"]<3 for r in receipts)
    return {"pairs":[list(p) for p in PAIRS],
            "times":[round(o[1],3) for o in opts],
            "minimum_training_harmonic_magnitudes":[o[3] for o in opts],
            "replicates":2000,"seed":SEED,"results":receipts,
            "scope":"Ideal isolated-face readout. Independent calibration reference per face; no hardware noise model. Tests consistency of separately implemented masked faces, not unconstrained closure of a single static intact Hamiltonian."}


def order_memory():
    """Four logical qubits: cube position and one internal SU(2) mode."""
    I=np.eye(2,dtype=complex)
    X=np.array([[0,1],[1,0]],complex)
    Y=np.array([[0,-1j],[1j,0]],complex)
    Z=np.diag([1,-1]).astype(complex)
    A=(0,1,3,2,0); B=(0,1,5,4,0)
    def link(u,v,U):
        T=np.eye(16,dtype=complex); a=slice(2*u,2*u+2); b=slice(2*v,2*v+2)
        T[a,a]=T[b,b]=0; T[b,a]=U; T[a,b]=U.conj().T
        np.testing.assert_allclose(T.conj().T@T,np.eye(16),atol=1e-12)
        return T
    def walk(path,links):
        T=np.eye(16,dtype=complex)
        for u,v in zip(path,path[1:]):
            U=links.get(tuple(sorted((u,v))),I)
            T=link(u,v,U if u<v else U.conj().T)@T
        return T
    def evaluate(alpha,beta,axis):
        links={(1,3):np.cos(alpha)*I+1j*np.sin(alpha)*X,
               (1,5):np.cos(beta)*I+1j*np.sin(beta)*axis}
        W_A,W_B=walk(A,links),walk(B,links)
        np.testing.assert_allclose(walk(A[::-1],links),W_A.conj().T,atol=1e-12)
        np.testing.assert_allclose(walk(B[::-1],links),W_B.conj().T,atol=1e-12)
        psi=np.zeros(16,complex);psi[0]=1
        ab=(W_B@W_A@psi).reshape(8,2);ba=(W_A@W_B@psi).reshape(8,2)
        np.testing.assert_allclose(ab[1:],0,atol=1e-12)
        np.testing.assert_allclose(ba[1:],0,atol=1e-12)
        distance=float(np.sqrt(max(0,1-abs(np.vdot(ab,ba))**2)))
        return distance,[float(np.vdot(ab[0],Y@ab[0]).real),float(np.vdot(ba[0],Y@ba[0]).real)]
    d,y=evaluate(np.pi/4,np.pi/2,Z)
    np.testing.assert_allclose([d,*y],[1,-1,1],atol=1e-12)
    for alpha,beta in np.random.default_rng(SEED).uniform(-np.pi,np.pi,(20,2)):
        distance,_=evaluate(alpha,beta,Z)
        np.testing.assert_allclose(distance,abs(np.sin(2*alpha)*np.sin(beta)),atol=1e-10)
    dc,_=evaluate(np.pi/4,np.pi/2,X)
    assert dc<1e-7
    return {"routes":{"A":A,"B":B},"ideal_trace_distance":d,
            "Y_expectation_AB_then_BA":y,"ideal_commuting_trace_distance":dc,
            "spatial_return_both":1.0,"random_angle_checks":20,
            "scope":"Ideal routed link-swap construction. No physical compilation or noise results."}


def main():
    report={"evidence":"offline analysis of frozen Q3 receipts and ideal new simulations",
            "hardware_diagnostics":hardware_diagnostics(),"intact_consistency":intact_consistency(),
            "masked_face_design":masked_design(),"order_memory":order_memory(),
            "hardware_decision":"HOLD for new QPU submissions"}
    print(json.dumps(report,indent=2,allow_nan=False))


if __name__=="__main__":
    main()
