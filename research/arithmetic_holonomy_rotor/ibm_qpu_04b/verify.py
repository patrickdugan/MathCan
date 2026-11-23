"""AHR-QPU-04B: archived counts, bounded descriptive fits, and ideal controls.

Standard library only. No credentials, QPU client, network calls or submission.
"""
import argparse
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "ibm_qpu_04" / "receipts"
JOB = "dc2b0g5s2omc738bn0d0"
TIMES = (0, 2, 8, 24)
ARMS = ("signal", "direct", "order_register")
LABELS = ("AB", "BA")


def load(name):
    return json.loads((SOURCE / name).read_text(encoding="utf-8"))


def case_id(arm, time, label):
    if not time:
        return f"{arm}/{label}"
    prefix = "memory" if arm == "signal" else f"{arm}_memory"
    return f"{prefix}/{time}/{label}"


def endpoint(counts, label):
    n = sum(counts.values())
    plus, minus = counts.get("0000", 0), counts.get("1000", 0)
    ret = plus + minus
    correct = minus if label == "AB" else plus
    return dict(shots=n, positive=plus, negative=minus, returns=ret,
                joint=correct/n, spatial_return=ret/n,
                conditional_correct=correct/ret, Y=(plus-minus)/ret)


def total_variation(a, b):
    return .5*sum(abs(x-y) for x,y in zip(a,b,strict=True))


def wilson(k, n):
    z=1.959963984540054
    p=k/n
    d=1+z*z/n
    mid=(p+z*z/(2*n))/d
    rad=z*math.sqrt(p*(1-p)/n+z*z/(4*n*n))/d
    return [max(0,mid-rad),min(1,mid+rad)]


def profile_data(manifest, hardware):
    ids=[r["case"]["id"] for r in manifest["cases"]]
    assert len(ids)==len(set(ids))==76
    assert hardware["job_id"]==JOB and hardware["pub_case_ids_match"]
    assert ids==list(hardware["counts"])==hardware["pub_case_ids"]
    records={r["case"]["id"]:r for r in manifest["cases"]}
    for name,c in hardware["counts"].items():
        assert all(len(k)==4 and set(k)<={"0","1"} and isinstance(v,int) and v>=0
                   for k,v in c.items())
        assert sum(c.values())==records[name]["shots"]==2048
    assert sum(r["shots"] for r in records.values())==155648
    rows=[]
    for arm in ARMS:
        for time in TIMES:
            names=[case_id(arm,time,l) for l in LABELS]
            raw=[hardware["counts"][name] for name in names]
            ends=[endpoint(c,l) for c,l in zip(raw,LABELS,strict=True)]
            r0,r1=ends
            bins=[[c.get(f"{i:04b}",0)/2048 for i in range(16)] for c in raw]
            tri=[[r["positive"]/2048,r["negative"]/2048,1-r["spatial_return"]] for r in ends]
            pos=[r["positive"]/r["returns"] for r in ends]
            fixed=.5*sum(r["joint"]+.5*(1-r["spatial_return"]) for r in ends)
            rows.append(dict(arm=arm,dwell_us=time,AB=r0,BA=r1,
                conditional_Y_TV=abs(pos[0]-pos[1]),
                conditional_equal_prior_plugin_accuracy=.5*(1+abs(pos[0]-pos[1])),
                full_histogram_plugin_TV=total_variation(*bins),
                erasure_plugin_TV=total_variation(*tri),
                fixed_sign_decoder_random_erasure_accuracy=fixed,
                cases=[dict(id=name,measurement_by_classical_bit=records[name]["measurement_by_classical_bit"],
                      native_metrics=records[name]["metrics"]) for name in names]))
    return rows


def deviance(rows, predictions):
    result=0.
    for (t,k,n),y in zip(rows,predictions,strict=True):
        q=max(1e-12,min(1-1e-12,(1+y)/2))
        p=k/n
        if k:
            result+=2*k*math.log(p/q)
        if n-k:
            result+=2*(n-k)*math.log((1-p)/(1-q))
    return result


def weighted_linear(rows, a, b):
    xx=xz=zz=xy=zy=0.
    for (_,k,n),x,z in zip(rows,a,b,strict=True):
        y=2*k/n-1
        weight=n/max(1e-12,1-y*y)
        xx+=weight*x*x
        xz+=weight*x*z
        zz+=weight*z*z
        xy+=weight*x*y
        zy+=weight*z*y
    determinant=xx*zz-xz*xz
    if determinant<=1e-12:
        return None
    return ((xy*zz-zy*xz)/determinant,(zy*xx-xy*xz)/determinant)


def select_rotation(rows, t2_us):
    """Descriptive grid/profile WLS; select by binomial deviance, not exact MLE."""
    best=None
    g=1/t2_us
    for index in range(1,2501):
        frequency_khz=index*.04
        w=2*math.pi*frequency_khz/1000
        a=[math.exp(-g*t)*math.cos(w*t) for t,_,_ in rows]
        b=[math.exp(-g*t)*math.sin(w*t) for t,_,_ in rows]
        coefficients=weighted_linear(rows,a,b)
        if coefficients is None:
            continue
        c,s=coefficients
        amplitude=math.hypot(c,s)
        if amplitude>1:
            c,s=c/amplitude,s/amplitude
        prediction=[c*x+s*z for x,z in zip(a,b,strict=True)]
        score=deviance(rows,prediction)
        if best is None or score<best["deviance"]:
            best=dict(deviance=score,frequency_khz=frequency_khz,
                cosine=c,sine=s,amplitude=math.hypot(c,s),t2_us=t2_us,
                fitted_Y=prediction,
                prospective_Y={str(t):math.exp(-g*t)*(c*math.cos(w*t)+s*math.sin(w*t))
                               for t in (16,40)})
    return best


def select_decay(rows):
    """Bounded exploratory decay and biased-asymptote competitors."""
    pure=biased=None
    for index in range(401):
        g=index*.0005
        a=[math.exp(-g*t) for t,_,_ in rows]
        b=[1-x for x in a]
        ys=[2*k/n-1 for _,k,n in rows]
        weights=[n/max(1e-12,1-y*y) for (_,k,n),y in zip(rows,ys,strict=True)]
        u=sum(w*y*x for w,y,x in zip(weights,ys,a,strict=True))/sum(w*x*x for w,x in zip(weights,a,strict=True))
        u=max(-1,min(0,u))
        prediction=[u*x for x in a]
        score=deviance(rows,prediction)
        if pure is None or score<pure["deviance"]:
            pure=dict(deviance=score,gamma_per_us=g,initial=u,fitted_Y=prediction)
        coefficients=weighted_linear(rows,a,b)
        if coefficients is None:
            continue
        u,z=coefficients
        clip=lambda x:max(-1,min(1,x))
        candidates=((clip(u),clip(z)),(-1,clip(z)),(clip(u),1),(clip(u),-1))
        for c,s in candidates:
            prediction=[c*x+s*y for x,y in zip(a,b,strict=True)]
            score=deviance(rows,prediction)
            if biased is None or score<biased["deviance"]:
                biased=dict(deviance=score,gamma_per_us=g,initial=c,asymptote=s,
                            fitted_Y=prediction,
                            prospective_Y={str(t):s+(c-s)*math.exp(-g*t) for t in (16,40)})
    return dict(sign_preserving_decay=pure,biased_decay=biased)


def dot(a,b):
    return sum(x*y for x,y in zip(a,b,strict=True))


def dephase(r,k,n):
    d=dot(n,r)
    return [k*x+(1-k)*d*y for x,y in zip(r,n,strict=True)]


def rotz(r,phi):
    x,y,z=r
    return [math.cos(phi)*x-math.sin(phi)*y,math.sin(phi)*x+math.cos(phi)*y,z]


def rx_minus_halfpi(r):
    x,y,z=r
    return [x,z,-y]


def rx_pi(r):
    x,y,z=r
    return [x,-y,-z]


def trace_distance(a,b):
    return .5*math.sqrt(sum((x-y)**2 for x,y in zip(a,b,strict=True)))


def ideal_checks():
    y=[0.,1.,0.]
    z=[0.,0.,1.]
    n=[0.,2**-.5,2**-.5]
    for k in (0.,.2,.5,.9,1.):
        for phi in (0.,.4,math.pi,2.7):
            ab=rotz(rotz(dephase(y,k,z),phi),math.pi)
            ba=rx_minus_halfpi(rotz(dephase(z,k,z),phi))
            expected=.5*math.sqrt(max(0,1+k*k+2*k*math.cos(phi)))
            assert abs(trace_distance(ab,ba)-expected)<1e-12
            # Two X pulses preserve the logical frame and refocus deterministic Z.
            echoed=rx_pi(rotz(rx_pi(rotz(y,phi/2)),phi/2))
            assert max(abs(a-b) for a,b in zip(echoed,y,strict=True))<1e-12
        ab=rotz(dephase(y,k,n),math.pi)
        ba=rx_minus_halfpi(dephase(z,k,n))
        assert abs(trace_distance(ab,ba)-math.sqrt((1+k*k)/2))<1e-12
        assert abs((1-ab[1])/2-(3+k)/4)<1e-12
        assert abs((1+ba[1])/2-(3+k)/4)<1e-12
    return {"tests":"ideal Bloch-channel algebra passed", "fixed_Y_balanced_worst_accuracy":"(3+kappa)/4",
            "standard_worst_accuracy":"(1+kappa)/2",
            "balanced_trace_distance":"sqrt((1+kappa**2)/2)",
            "standard_rotating_trace_distance":"sqrt(1+kappa**2+2*kappa*cos(phi))/2",
            "scope":"Common Z rotation and dephasing model; no hardware protection claim."}


def design(rows):
    """Prospective case ledger. Actual placement and timing MUST be regenerated."""
    cases=[]
    def add(arm,label,dwell,basis,intervention,shots=1024):
        key=f"{arm}/{label}/{dwell}/{basis}/{intervention}"
        cases.append(dict(id=key,arm=arm,label=label,dwell_us=dwell,basis=basis,
                          intervention=intervention,shots=shots))
    for arm in ("routed_full","direct_dwell_site"):
        for label in LABELS:
            for dwell in (0,8,16,24,40):
                for basis in "XYZ":
                    add(arm,label,dwell,basis,"idle")
            for dwell in (8,24):
                for basis in "XYZ":
                    add(arm,label,dwell,basis,"echo")
                add(arm,label,dwell,"Y","pulse_sham")
    for label in LABELS:
        for dwell in (0,24):
            for basis in "XYZ":
                add("routed_mid",label,dwell,basis,"idle")
    for bits in range(16):
        add("basis_prepare",f"{bits:04b}",0,"Z","prepare")
    assert len(cases)==120 and len({c["id"] for c in cases})==120
    # Max four actual involved sites, six eigenstate calibration settings/site.
    # Actual site set comes from the QPY audit; these are budget placeholders.
    extra=24*512
    nominal_shots=sum(c["shots"] for c in cases)
    # Historical schedule: largest prior routed base 12.616 us; add
    # 40 us dwell and 2 us intervention/basis slack. Engineering-only bound.
    max_circuit_seconds=(12.616+40+2)*1e-6
    rep_delay=.00025
    cap=math.ceil(2*(15+(nominal_shots+extra)*(max_circuit_seconds+rep_delay)))
    return dict(status="HOLD_UNCOMPILED_UNAUTHORIZED",
        seed=20261124, cases=cases, fixed_circuit_count=len(cases),
        fixed_shots=nominal_shots, optional_site_eigenstate_calibration_max_circuits=24,
        maximum_planned_shots=nominal_shots+extra,
        provisional_cap_seconds=cap, historical_rep_delay_s=rep_delay,
        historical_max_route_duration_assumption_s=max_circuit_seconds,
        warning="Engineering placeholder, not provider estimate or approval. Recompile frozen route with placement audit, fresh calibration and exact manifest before reconsidering.")


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    m,h=load("manifest.json"),load("hardware/counts.json")
    rows=profile_data(m,h)
    calibration=load("hardware/calibration_comparison.json")["job_start_values"]
    fits={}
    for arm in ARMS:
        sub=[r for r in rows if r["arm"]==arm]
        data=[(r["dwell_us"],r["AB"]["positive"],r["AB"]["returns"]) for r in sub]
        q=sub[0]["cases"][0]["measurement_by_classical_bit"][3]
        t2=calibration[f"q{q}/coherence_s"][1]*1e6
        fits[arm]=dict(final_readout_site=q,t2_reference_us=t2,
                       rotation=select_rotation(data,t2),**select_decay(data))
    r24=next(r for r in rows if r["arm"]=="signal" and r["dwell_us"]==24)
    assert r24["AB"]["positive"]==1493 and r24["AB"]["returns"]==1639
    assert abs(r24["conditional_equal_prior_plugin_accuracy"]-.5270439573157508)<1e-12
    assert all(f["rotation"]["deviance"]<f["sign_preserving_decay"]["deviance"] for f in fits.values())
    result=dict(status="PASS_OFFLINE_DIAGNOSTICS",job=JOB,shots=155648,
                rows=rows,descriptive_fits=fits,ideal=ideal_checks(),design=design(rows),
                limits="Four dwell observations per arm; descriptive, frequency aliasing, fixed final-site T2 reference not measured dwell-site T2. No process identification or independent decoder validation.")
    payload=json.dumps(result,indent=2,allow_nan=False)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(payload,encoding="utf-8")
    print(json.dumps({k:result[k] for k in ("status","job","shots","descriptive_fits","ideal")},indent=2))
    print(json.dumps({k:v for k,v in result["design"].items() if k!="cases"},indent=2))


if __name__=="__main__":
    main()
