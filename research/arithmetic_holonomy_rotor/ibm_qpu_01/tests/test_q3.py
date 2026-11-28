import numpy as np
from q3_curvature import (EDGES,TREE,CHORDS,BIANCHI,CONTROLS,
                          curl_matrix,faces,face_fluxes,bianchi_residual,
                          project_bianchi,reconstruct_chords,addressable_faces,
                          measured_face_phase)
from phase_estimator import wrap


def test_integer_cubical_incidence_and_schedule():
    curl=curl_matrix()
    assert curl.shape==(6,12)
    assert np.all(BIANCHI@curl==0)
    assert np.linalg.matrix_rank(curl)==5
    assert len(TREE)==7 and len(CHORDS)==5
    schedule=addressable_faces()
    assert len(schedule)==6
    assert len(set(e for _,e,_ in schedule))==3
    assert set(e for _,e,_ in schedule)==set(CONTROLS)


def test_reconstruction_gauge_fixed_edges():
    rng=np.random.default_rng(20261123)
    arr=rng.uniform(-.4,.4,len(EDGES))
    rec=reconstruct_chords(face_fluxes(arr))
    # BFS root 0: vertex gauge eliminates all seven tree edge phases.
    tree_neigh={i:[] for i in range(8)}
    for a,b in TREE:
        tree_neigh[a].append((b,1));tree_neigh[b].append((a,-1))
    amap={e:arr[i] for i,e in enumerate(EDGES)}
    chi={0:0.};queue=[0]
    for u in queue:
        for v,sgn in tree_neigh[u]:
            if v in chi:continue
            e=(min(u,v),max(u,v))
            chi[v]=chi[u]-sgn*amap[e]
            queue.append(v)
    expected=wrap([amap[a,b]+chi[b]-chi[a] for a,b in CHORDS])
    assert np.allclose(wrap(rec-expected),0,atol=1e-12)


def test_projection_covariance():
    arr=np.random.default_rng(2).uniform(-.25,.25,12)
    flux=face_fluxes(arr)
    noisy=wrap(flux+np.array([.02,-.03,.005,.07,-.025,.045]))
    projected=project_bianchi(noisy)
    assert abs(bianchi_residual(projected))<1e-12
    cov=np.diag([1,2,3,4,5,6.])
    assert abs(bianchi_residual(project_bianchi(noisy,cov)))<1e-12


def test_full_cube_face_addressability_short_time():
    arr=np.random.default_rng(20261123).uniform(-.25,.25,12)
    for fi in range(6):
        r=measured_face_phase(arr,fi,.12)
        assert abs(r['angular_error'])<.004
