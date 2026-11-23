"""AHR-08/09 oriented cubical cochains and face-phase estimation on Q3."""
from __future__ import annotations
import numpy as np
from exact_oracle import exact_probabilities, PHASE_OFFSETS
from phase_estimator import quadrature, wrap
from hamiltonian import hypercube_hamiltonian

EDGES=tuple((a,a|(1<<i)) for a in range(8) for i in range(3) if not (a>>i)&1)
TREE=((0,1),(0,2),(0,4),(1,3),(1,5),(2,6),(3,7))
CHORDS=tuple(e for e in EDGES if e not in TREE)
BIANCHI=np.array([-1,1,1,-1,-1,1],dtype=int)
CONTROLS=((0,1),(2,6),(5,7))


def faces():
    """Faces in AHR-09 order: (01,z=0/1), (02,y=0/1), (12,x=0/1)."""
    ans=[]
    for i,j in ((0,1),(0,2),(1,2)):
        k=3-i-j
        for bit in (0,1):
            a=bit*(1<<k)
            b=a|(1<<i); c=a|(1<<j); d=a|(1<<i)|(1<<j)
            ans.append((a,b,d,c))
    return tuple(ans)


def curl_matrix():
    emap={edge:i for i,edge in enumerate(EDGES)}
    mat=np.zeros((6,12),dtype=int)
    for fi,face in enumerate(faces()):
        for u,v in zip(face,face[1:]+face[:1]):
            e=(min(u,v),max(u,v))
            mat[fi,emap[e]] += 1 if u<v else -1
    return mat


def face_fluxes(edge_angles:np.ndarray):
    return wrap(curl_matrix()@np.asarray(edge_angles))


def bianchi_residual(measured:np.ndarray)->float:
    return float(wrap(BIANCHI@measured))


def project_bianchi(measured:np.ndarray,covariance:np.ndarray|None=None):
    """Local wrapped projection; branch consistency required near +/-pi."""
    v=np.asarray(measured,dtype=float)
    cov=np.eye(6) if covariance is None else np.asarray(covariance)
    b=BIANCHI.astype(float)
    residual=bianchi_residual(v)
    correction=(cov@b)*residual/(b@cov@b)
    return wrap(v-correction)


def reconstruct_chords(measured:np.ndarray):
    """Reconstruct five gauge-fixed chord phases, omitting the last face."""
    emap={edge:i for i,edge in enumerate(EDGES)}
    columns=[emap[e] for e in CHORDS]
    mat=curl_matrix()[:5,columns]
    if abs(round(np.linalg.det(mat)))!=1: raise ValueError('Unimodular inverse failed')
    return wrap(np.linalg.solve(mat,np.asarray(measured)[:5]))


def addressable_faces():
    """For every face return a controllable edge and an opposite starting corner."""
    schedule=[]
    for fi,face in enumerate(faces()):
        selected=None
        for e in CONTROLS:
            if e[0] in face and e[1] in face:
                # Select corner not on the controlled edge, incident to the edge's lower endpoint.
                for x in face:
                    if x in e: continue
                    if (x^e[0]).bit_count()==1:
                        selected=(fi,e,x); break
            if selected: break
        if selected is None: raise ValueError(f'No edge for face {fi}')
        schedule.append(selected)
    return schedule


def measured_face_phase(edge_angles:np.ndarray,face_index:int,time:float,j:float=1.):
    """Return signed angle from the full Q3 Hamiltonian with a four-phase edge scan.

    Control-edge phase sign depends on orientation, so convert the measured
    quadrature to the orientation defined by the face boundary.
    """
    schedule=addressable_faces()
    fi,e,x=schedule[face_index]
    assert fi==face_index
    edge_dict={edge:float(a) for edge,a in zip(EDGES,edge_angles)}
    vals=[]
    for delta in PHASE_OFFSETS:
        phased=dict(edge_dict);phased[e]+=delta
        vals.append(float(exact_probabilities(hypercube_hamiltonian(3,phased,j=j),time,x)[x]))
    z=quadrature(vals)
    face=list(faces()[fi]); orientation=0
    for u,v in zip(face,face[1:]+face[:1]):
        if set((u,v))==set(e):
            orientation=1 if u<v else -1
            break
    if orientation==0: raise AssertionError('Controlled edge absent from target face')
    # The z response is exp(i orientation*F) if the controlled edge has sign
    # in the directed cycle; an orientation flip is therefore needed for -1.
    estimate=wrap(orientation*np.angle(z))
    true=face_fluxes(edge_angles)[fi]
    return {'face':fi,'edge':e,'start':x,'true_phase':float(true),
            'measured_phase':float(estimate), 'angular_error':float(wrap(estimate-true)),
            'complex_quadrature':[float(z.real),float(z.imag)]}


def measurement_schedule():
    return [{'face':fi,'control_edge':list(e),'initial_state':x,
             'offsets':[float(v) for v in PHASE_OFFSETS]} for fi,e,x in addressable_faces()]
