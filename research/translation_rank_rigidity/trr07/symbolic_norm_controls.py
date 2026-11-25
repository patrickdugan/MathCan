#!/usr/bin/env python3
"""Fail-closed corruption controls for the independent elimination replay."""
import argparse
import copy
import hashlib
import json
import tempfile
import time
from pathlib import Path
from symbolic_norm_replay import replay


def run(certificate):
    start=time.monotonic()
    original=json.loads(certificate.read_text())
    assert set(original)=={"19"}, "the bounded control fixture must have order19"
    positive=replay(certificate)
    mutations={}
    a=copy.deepcopy(original)
    a["19"]["P"]["2"][0]=str(int(a["19"]["P"]["2"][0])+1)
    mutations["norm_coefficient"]=a
    a=copy.deepcopy(original)
    a["19"]["W"]["2"][0]=str(int(a["19"]["W"]["2"][0])+1)
    mutations["bezout_coefficient"]=a
    a=copy.deepcopy(original)
    a["19"]["n0"]=str(int(a["19"]["n0"])+1)
    mutations["integer_constant"]=a
    a=copy.deepcopy(original)
    del a["19"]["primes"]["19"]
    mutations["missing_characteristic"]=a
    a=copy.deepcopy(original)
    factor=a["19"]["primes"]["19"]["factors"][0]
    factor["phi"][0]=str((int(factor["phi"][0])+1)%19)
    mutations["wrong_norm_factor"]=a
    a=copy.deepcopy(original)
    factor=a["19"]["primes"]["19"]["factors"][0]
    factor["Gamma"][0][0]=str((int(factor["Gamma"][0][0])+1)%19)
    mutations["wrong_fibre_gcd"]=a
    a=copy.deepcopy(original)
    a["19"]["primes"]["19"]["factors"][0]["discriminant_power"]=0
    mutations["wrong_discriminant_power"]=a
    a=copy.deepcopy(original)
    a["19"]["g"]["2"]["num"][0][0]=str(int(a["19"]["g"]["2"]["num"][0][0])+1)
    mutations["wrong_compressed_equation"]=a
    mutations["empty_certificate"]={}
    records=[]
    with tempfile.TemporaryDirectory() as temporary:
        for name,case in mutations.items():
            path=Path(temporary)/(name+".json")
            path.write_text(json.dumps(case))
            try:
                replay(path)
            except Exception as error:
                records.append({"case":name,"rejected":True,"error_type":type(error).__name__})
            else:
                raise AssertionError(name+" unexpectedly accepted")
    return {"schema":"trr07-elimination-mutations-v1","status":"passed",
            "positive_control":"order19","mutations":records,
            "elapsed_seconds":time.monotonic()-start,
            "certificate_sha256":hashlib.sha256(certificate.read_bytes()).hexdigest()}


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("certificate",type=Path)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    result=run(args.certificate)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result))
