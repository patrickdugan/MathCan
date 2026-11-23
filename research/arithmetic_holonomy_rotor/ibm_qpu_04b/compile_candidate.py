"""Compile 04B candidates by editing native archived QPY at protected boundaries.

Offline only. No live calibration, IBM SDK login, or submission. All candidates
are historical-snapshot simulation artifacts and remain HOLD.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np
from qiskit import ClassicalRegister, QuantumCircuit, qpy

ROOT=Path(__file__).resolve().parent
PARENT=ROOT.parent/"ibm_qpu_04"
sys.path.insert(0,str(PARENT))
from circuits import compact_target, ideal_probability, measurement_map, physical_circuit, timing
from noise import probabilities

from qpy_audit import audit as placement_audit
from verify import design, load

SEED=20261124
FREQUENCIES=(8.96,18.04)
AXES="XYZ"
LABELS=("AB","BA")


def write(path,value):
    path.write_text(json.dumps(value,indent=2,allow_nan=False)+"\n",encoding="utf-8")


def filehash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def native_h(c,q):
    # Rz(pi/2) SX Rz(pi/2) = H up to global phase.
    c.rz(np.pi/2,q)
    c.sx(q)
    c.rz(np.pi/2,q)


def basis(c,q,b):
    if b=="Y":
        c.rz(-np.pi/2,q)
    if b in ("X","Y"):
        native_h(c,q)
    elif b!="Z":
        raise ValueError("unknown readout basis")


def loop(c,q,label):
    if label=="A":
        # Rz(pi) SX Rz(-pi) = Rx(-pi/2) up to phase.
        c.rz(np.pi,q)
        c.sx(q)
        c.rz(-np.pi,q)
    elif label=="B":
        c.rz(-np.pi,q)
    else:
        raise ValueError("unknown loop")


def archive_blocks(circuit,physical):
    lookup={p:i for i,p in enumerate(physical)}
    blocks=[[],[]]
    edges=[]
    for item in circuit.data:
        op=item.operation
        sites=[circuit.find_bit(q).index for q in item.qubits]
        if op.name in ("delay","measure"):
            raise ValueError("unexpected delay or measure before eight protected edges")
        qargs=[lookup[q] for q in sites]
        blocks[len(edges)//4].append((op,qargs))
        if op.name=="barrier" and op.label and op.label.startswith("edge_"):
            edges.append(op.label)
            if len(edges)==8:
                break
    if len(edges)!=8 or not all(s.startswith("edge_0_") for s in edges[:4]) or not all(
            s.startswith("edge_1_") for s in edges[4:]):
        raise ValueError("archived route boundaries changed")
    return blocks,edges


def copy_block(c,block):
    for op,qs in block:
        c.append(op,qs)


def block_duration(block,target):
    c=QuantumCircuit(4)
    copy_block(c,block)
    return timing(c,target)["duration_s"]


def pad(c,duration,dt,label):
    ticks=round(max(0.,duration)/dt)
    if ticks:
        c.barrier(range(4),label=label+"_start")
        c.delay(ticks,range(4),unit="dt")
        c.barrier(range(4),label=label+"_end")


def idle_segment(c,mode,ticks,dt,frequency):
    if ticks:
        c.delay(ticks,range(4),unit="dt")
        c.barrier(range(4))
        if frequency:
            # Artificial phase in simulation stress only; never emit in candidate QPY.
            c.rz(2*np.pi*frequency*1000*ticks*dt,mode)
            c.barrier(range(4))


def dwell(c,q,time,intervention,dt,frequency=0.):
    ticks=round(time*1e-6/dt)
    c.barrier(range(4),label="04b_dwell_start")
    if intervention=="echo":
        a=ticks//2
        idle_segment(c,q,a,dt,frequency)
        c.x(q)
        c.barrier(range(4),label="04b_echo_midpoint")
        idle_segment(c,q,ticks-a,dt,frequency)
        c.x(q)
        c.barrier(range(4),label="04b_echo_restore")
    elif intervention=="pulse_sham":
        idle_segment(c,q,ticks,dt,frequency)
        c.x(q)
        c.barrier(range(4),label="04b_sham_pulse1")
        c.x(q)
        c.barrier(range(4),label="04b_sham_pulse2")
    elif intervention=="idle":
        idle_segment(c,q,ticks,dt,frequency)
    else:
        raise ValueError("unknown intervention")
    c.barrier(range(4),label="04b_dwell_end")


def register_measure(c,logical_to_compact):
    c.add_register(ClassicalRegister(4,"out"))
    c.measure(logical_to_compact,range(4))


def expected(case):
    if case["arm"]=="basis_prepare":
        return int(case["label"],2)
    if case["arm"]=="site_eigenstate":
        return 0 if case["eigenvalue"]==1 else 8
    if case["arm"]=="routed_mid":
        return 0 if ((case["basis"]=="Y" and case["label"]=="AB") or
                     (case["basis"]=="Z" and case["label"]=="BA")) else None
    if case["basis"]=="Y":
        return 8 if case["label"]=="AB" else 0
    return None


def get_schedule(manifest,circuits,physical,target):
    schedule={}
    for circuit,record in zip(circuits,manifest["cases"],strict=True):
        case=record["case"]
        if case["id"] not in ("signal/AB","signal/BA"):
            continue
        blocks,edges=archive_blocks(circuit,physical)
        mapping=[physical.index(q) for q in record["measurement_by_classical_bit"]]
        schedule[case["label"]]=dict(blocks=blocks,edges=edges,mapping=mapping,
            durations=[block_duration(b,target) for b in blocks])
    assert set(schedule)==set(LABELS)
    return schedule


def make(case,schedule,physical,target,dt,dwell_site,frequency=0.):
    c=QuantumCircuit(4,name=case["id"].replace("/","_"))
    q=physical.index(dwell_site)
    canonical=[i for i in range(4) if i!=q]+[q]
    arm=case["arm"]
    if arm=="basis_prepare":
        mapping=canonical
        bits=int(case["label"],2)
        for j,k in enumerate(mapping):
            if bits>>j&1:
                c.x(k)
    elif arm=="site_eigenstate":
        q=physical.index(case["site"])
        mapping=[i for i in range(4) if i!=q]+[q]
        if case["eigenvalue"]==-1:
            c.x(q)
        if case["basis"] in ("X","Y"):
            native_h(c,q)
        if case["basis"]=="Y":
            c.rz(np.pi/2,q)
        basis(c,q,case["basis"])
    else:
        label=case["label"]
        plan=schedule[label]
        if arm.startswith("routed"):
            copy_block(c,plan["blocks"][0])
        elif arm=="direct_dwell_site":
            # Both time windows match native routed durations, within dt rounding.
            # Padding is before W_first and after W_second; differing history
            # during these windows is a documented limitation.
            temp=QuantumCircuit(4)
            loop(temp,q,label[0])
            pad(c,plan["durations"][0]-timing(temp,target)["duration_s"],dt,"direct_pre")
            loop(c,q,label[0])
        else:
            raise ValueError("unknown arm")
        dwell(c,q,case["dwell_us"],case["intervention"],dt,frequency)
        if arm=="routed_full":
            copy_block(c,plan["blocks"][1])
            mapping=plan["mapping"]
            if mapping[3]!=q:
                raise ValueError("final site differs from certified dwell site")
        elif arm=="routed_mid":
            mapping=canonical
        else:
            loop(c,q,label[1])
            temp=QuantumCircuit(4)
            loop(temp,q,label[1])
            pad(c,plan["durations"][1]-timing(temp,target)["duration_s"],dt,"direct_post")
            mapping=plan["mapping"]
        basis(c,q,case["basis"])
    register_measure(c,mapping)
    c.metadata={"case_id":case["id"],"case":case,"frequency_stress_khz":frequency}
    return c


def checked_probability(c,case):
    p=ideal_probability(c)
    if abs(p.sum()-1)>1e-10:
        raise ValueError("invalid ideal probability")
    if case["arm"] not in ("basis_prepare","site_eigenstate"):
        e=expected(case)
        goal=np.zeros(16)
        if e is None:
            goal[[0,8]]=.5
        else:
            goal[e]=1
    else:
        goal=np.eye(16)[expected(case)]
    np.testing.assert_allclose(p,goal,atol=1e-10,rtol=0)
    return p


def check_route_blocks(c,case,schedule):
    if not case["arm"].startswith("routed"):
        return
    keep=4 if case["arm"]=="routed_mid" else 8
    labels=[item.operation.label for item in c.data if item.operation.name=="barrier"
            and item.operation.label and item.operation.label.startswith("edge_")]
    assert labels==schedule[case["label"]]["edges"][:keep]
    # Compare every native gate in each archived edge block, including its qubits.
    old=[pair for block in schedule[case["label"]]["blocks"][:keep//4] for pair in block]
    # Locate boundaries in edited circuit. Remove precisely the intervention
    # region, not any gate with a matching name.
    new=[]
    inside=False
    seen=0
    for item in c.data:
        label=item.operation.label
        if item.operation.name=="barrier" and label=="04b_dwell_start":
            inside=True
            continue
        if item.operation.name=="barrier" and label=="04b_dwell_end":
            inside=False
            if seen==keep:
                break
            continue
        if inside:
            continue
        new.append((item.operation,[c.find_bit(q).index for q in item.qubits]))
        if item.operation.name=="barrier" and label and label.startswith("edge_"):
            seen+=1
            if seen==keep:
                break
    assert len(new)==len(old)
    for (a,aq),(b,bq) in zip(new,old,strict=True):
        assert a==b and aq==bq


def readout(p,case):
    ret=float(p[0]+p[8])
    y=float((p[0]-p[8])/ret) if ret else None
    correct=float(p[8 if case["label"]=="AB" else 0]) if case["basis"]=="Y" and case["arm"] in (
        "routed_full","direct_dwell_site") else None
    return dict(spatial_return=ret,conditional_axis_expectation=y,joint_correct=correct)


def compare(rows):
    result={}
    for arm in ("routed_full","direct_dwell_site"):
        for t in (8,24):
            labels={}
            for label in LABELS:
                get=lambda k:rows[f"{arm}/{label}/{t}/Y/{k}"]["joint_correct"]
                labels[label]=dict(idle=get("idle"),echo=get("echo"),sham=get("pulse_sham"),
                    echo_gain_over_sham=get("echo")-get("pulse_sham"))
            result[f"{arm}/{t}"]=labels
    return result


def run(out):
    out.mkdir(parents=True,exist_ok=True)
    parent=load("manifest.json")
    certified=placement_audit()
    sites={r["dwell_site"] for r in certified["rows"]}
    assert sites=={16} and all(r["final_site"]==16 for r in certified["rows"])
    site=next(iter(sites))
    inventory=load("calibration.json")
    winner=load("compilation.json")["selected"]
    snapshot=inventory["snapshots"][winner["snapshot_index"]]
    physical=parent["physical_qubits"]
    assert snapshot["selection"]["physical_xyz"]==physical
    target=compact_target(snapshot)
    dt=snapshot["dt_s"]
    with (PARENT/"receipts"/"q4_candidate_isa.qpy").open("rb") as stream:
        old=qpy.load(stream)
    schedule=get_schedule(parent,old,physical,target)
    cases=design([])["cases"]
    for s in certified["calibration_sites"]:
        for axis in AXES:
            for sign in (1,-1):
                cases.append(dict(id=f"site_eigenstate/q{s}/{axis}/{sign:+d}",arm="site_eigenstate",
                    label=str(sign),dwell_us=0,basis=axis,intervention="prepare",
                    shots=512,site=s,eigenvalue=sign))
    assert len(cases)==132 and sum(x["shots"] for x in cases)==129024
    compact=[make(c,schedule,physical,target,dt,site) for c in cases]
    ideal=[checked_probability(q,c) for q,c in zip(compact,cases,strict=True)]
    for q,c in zip(compact,cases,strict=True):
        check_route_blocks(q,c,schedule)
        if c["arm"]=="routed_full":
            assert timing(q,target)["two_qubit_count"]==104
    nominal=probabilities(compact,snapshot)
    records=[]
    for q,c,p,a in zip(compact,cases,ideal,nominal,strict=True):
        records.append(dict(case=c,shots=c["shots"],metrics=timing(q,target),
            physical_by_classical_bit=[physical[k] for k in measurement_map(q)],
            ideal_distribution=p.tolist(),historical_aer_distribution=a.tolist()))
    nominal_rows={c["id"]:readout(p,c) for c,p in zip(cases,nominal,strict=True)}
    stress_cases=[c for c in cases if c["arm"] in ("routed_full","direct_dwell_site")
                  and c["basis"]=="Y" and c["dwell_us"] in (8,24)
                  and c["intervention"] in ("idle","echo","pulse_sham")]
    stress={}
    for freq in FREQUENCIES:
        cc=[make(c,schedule,physical,target,dt,site,freq) for c in stress_cases]
        # Echo/sham exact channel algebra is independently checked by verify.py.
        # Inserted Rz is a deliberately imposed simulator stress, not a new
        # physical claim or an operation included in the candidate QPY.
        noisy=probabilities(cc,snapshot)
        d={c["id"]:readout(p,c) for c,p in zip(stress_cases,noisy,strict=True)}
        stress[str(freq)]=compare(d)
    order=np.random.default_rng(SEED).permutation(len(cases))
    bundle=out/"q4b_candidate_isa.qpy"
    with bundle.open("wb") as stream:
        qpy.dump([physical_circuit(compact[i],snapshot) for i in order],stream)
    rows=[records[i] for i in order]
    rep=snapshot["rep_delay_s"]
    if rep is None:
        raise ValueError("historical snapshot lacks repetition delay")
    estimate=15+sum(r["shots"]*(r["metrics"]["duration_s"]+rep) for r in rows)
    result=dict(study="AHR-QPU-04B",status="HOLD_HISTORICAL_SIMULATION_ONLY",
        source_job=parent.get("job_id","dc2b0g5s2omc738bn0d0"),
        parent_qpy_sha256=parent["qpy_sha256"],candidate_qpy_sha256=filehash(bundle),
        calibration_timestamp=snapshot["calibration_timestamp"],physical_qubits=physical,
        certified_dwell_site=site,route_segment_durations_s={k:v["durations"] for k,v in schedule.items()},
        circuit_count=len(rows),shots=sum(r["shots"] for r in rows),random_order_seed=SEED,
        estimate_seconds_historical=estimate,provisional_cap_seconds=math.ceil(2*estimate),
        new_live_balance_verified=False,hardware_approval=False,qpu_submitted=False,
        cases=rows)
    write(out/"candidate_manifest.json",result)
    report=dict(status="PASS_HISTORICAL_COMPILATION_AND_IDEAL_ORACLE",
        circuit_count=len(rows),shots=result["shots"],provisional_cap_seconds=result["provisional_cap_seconds"],
        physical_qubits=physical,certified_dwell_site=site,
        route_segment_durations_s=result["route_segment_durations_s"],
        nominal=compare(nominal_rows),deliberately_imposed_detuning_stress=stress,
        caveats="Archived noise model; stress frequencies exploratory. No fresh calibration or confirmed improvement on hardware. Direct duration matching retains different state exposure. HOLD.")
    write(out/"simulation_summary.json",report)
    print(json.dumps(report,indent=2))


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    run(args.out)
