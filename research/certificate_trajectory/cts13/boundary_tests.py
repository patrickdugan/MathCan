"""Additional exact finite checks: bounded memo eviction and receipt replacement."""
import json
from pathlib import Path
from fractions import Fraction as F
import numpy as np
import cts13 as c
from cts13 import ref

def check():
    A=np.array([[1,0],[0,1],[-1,0],[0,-1]],dtype=np.int64)
    rhs=np.array([4,5,4,5],dtype=np.int64)
    v=np.array([2,-1],dtype=np.int64)
    B=np.column_stack((A@v,[1,2,0,0],[0,3,0,0]))
    api=c.API(A,rhs,B,v);safe=ref.SafeMat(A);st=c.stats()
    entry=c.Entry(api,safe,np.array([0,1]),st);entry.compile(safe,st)
    u=np.array([1,2,3]);s=api.factor(u,st);old=None;eviction=exact=stale=0
    for i in [1,2,3,4,5,1,6,2,7,1,1]:
        z=c.objective(np.array([i,1]),2)
        result=entry.check(safe,api,s,z,'memo',st);assert result is not None
        receipt=api.quote(s,z,entry,result,st)
        x=entry.vertex(u,c.stats());assert result[0]==str(F(int(ref.obj(z)@x),entry.q))
        assert len(entry.memo)<=4;exact+=1
        if old is not None:
            try:api.settle(s,z,old,st)
            except ValueError:stale+=1
            else:raise AssertionError('replaced receipt accepted')
        old=receipt
    assert st['memo_evictions']>0 and st['memo_hits']>0
    # A fresh positive scaling changes the exact key even when the optimum stays fixed.
    # Settlement is checked under the current exact objective and receipt identity.
    return dict(exact_values=exact,replaced_receipts_rejected=stale,memo_evictions=st['memo_evictions'],memo_hits=st['memo_hits'],memo_misses=st['memo_misses'],maximum_capacity=4)
if __name__=='__main__':
    result=check();Path('boundary_audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result)
