"""Read-only QPY audit of the first-loop logical internal-mode placement.

Uses the original Q4 QPY and its digest. Simulates only four compact physical
qubits; no provider calls. A failure is HOLD rather than a guessed mapping.
"""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
from qiskit import QuantumCircuit, qpy
from qiskit.quantum_info import Statevector

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/"ibm_qpu_04"/"receipts"


def prefix_placement(circuit, physical, initial_site, label):
    index={q:k for k,q in enumerate(physical)}
    prefix=QuantumCircuit(4)
    edges=[]
    found=False
    for item in circuit.data:
        op=item.operation
        sites=[circuit.find_bit(q).index for q in item.qubits]
        if op.name=="barrier":
            if op.label and op.label.startswith("edge_"):
                edges.append(op.label)
                if len(edges)==4:
                    found=True
                    break
            continue
        if op.name in {"delay","measure"}:
            raise ValueError("unexpected delay or measurement before fourth protected edge")
        prefix.append(op,[index[q] for q in sites])
    if not found or not all(s.startswith("edge_0_") for s in edges):
        raise ValueError("first-loop edge boundaries absent")
    columns=[]
    for bit in (0,1):
        probe=QuantumCircuit(4)
        if bit:
            probe.x(index[initial_site])
        probe.compose(prefix,inplace=True)
        columns.append(np.asarray(Statevector.from_instruction(probe).data))
    C=np.column_stack(columns)
    if label=="AB":
        expected=np.array([[1,1j],[1j,1]])/np.sqrt(2)
    else:
        expected=np.diag([1j,-1j])
    candidates=[]
    for k,q in enumerate(physical):
        keep=[0,1<<k]
        remainder=np.delete(C,keep,axis=0)
        U=C[keep,:]
        overlap=np.vdot(expected,U)
        phase=overlap/abs(overlap) if abs(overlap)>1e-14 else 1
        error=float(np.linalg.norm(U-phase*expected))
        spill=float(np.linalg.norm(remainder))
        candidates.append(dict(site=q,error=error,spill=spill))
    best=min(candidates,key=lambda v:v["error"]+v["spill"])
    if best["error"]+best["spill"]>1e-8:
        raise ValueError(f"cannot certify dwell-site factorization: {best}")
    return best


def audit():
    manifest=json.loads((SOURCE/"manifest.json").read_text())
    archive=SOURCE/"q4_candidate_isa.qpy"
    assert hashlib.sha256(archive.read_bytes()).hexdigest()==manifest["qpy_sha256"]
    with archive.open("rb") as stream:
        circuits=qpy.load(stream)
    assert len(circuits)==len(manifest["cases"])==76
    physical=manifest["physical_qubits"]
    initial_site=manifest["initial_physical_by_logical"][3]
    rows=[]
    for circuit,record in zip(circuits,manifest["cases"],strict=True):
        c=record["case"]
        assert circuit.metadata["case_id"]==c["id"]
        if c["arm"]!="signal" or c["id"].startswith("heldout"):
            continue
        measured={circuit.find_bit(item.clbits[0]).index:circuit.find_bit(item.qubits[0]).index
                  for item in circuit.data if item.operation.name=="measure"}
        assert [measured[k] for k in range(4)]==record["measurement_by_classical_bit"]
        best=prefix_placement(circuit,physical,initial_site,c["label"])
        rows.append(dict(id=c["id"],label=c["label"],dwell_us=c["dwell_us"],
                         initial_site=initial_site,dwell_site=best["site"],
                         final_site=measured[3],operator_error=best["error"],
                         off_site_spill=best["spill"]))
    assert len(rows)==8
    return dict(status="PASS_QPY_PREFIX_PLACEMENT",job="dc2b0g5s2omc738bn0d0",
                qpy_sha256=manifest["qpy_sha256"],rows=rows,
                calibration_sites=sorted({r[k] for r in rows for k in ("dwell_site","final_site","initial_site")}),
                hardware_decision="HOLD")


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    report=json.dumps(audit(),indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(report,encoding="utf-8")
    print(report)
