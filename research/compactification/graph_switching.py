"""NRF-02: independent rational graph-cycle, path and covering oracle."""
from dataclasses import dataclass
from fractions import Fraction as Q

@dataclass(frozen=True)
class WeightedEdge:
    name: str
    src: str
    dst: str
    rate: Q

def validate(vertices: tuple[str, ...], edges: tuple[WeightedEdge, ...]) -> None:
    if not vertices or len(vertices)!=len(set(vertices)):
        raise ValueError("nonempty distinct vertices required")
    if len(set(e.name for e in edges))!=len(edges):
        raise ValueError("duplicate edge")
    if any(e.src not in vertices or e.dst not in vertices or e.rate<0 for e in edges):
        raise ValueError("bad endpoint or gain")

def cycle_products(vertices: tuple[str, ...],
                   edges: tuple[WeightedEdge, ...]) -> tuple[tuple[tuple[str, ...], Q], ...]:
    """Independent DFS enumeration of simple cycles; rotations allowed."""
    validate(vertices, edges)
    found=[]
    def dfs(start, current, visited, route, gain):
        for edge in edges:
            if edge.src != current:
                continue
            new_gain=gain*edge.rate
            if edge.dst == start:
                found.append((route+(edge.name,),new_gain))
            elif edge.dst not in visited:
                dfs(start, edge.dst, visited | {edge.dst},route+(edge.name,),new_gain)
    for vertex in vertices:
        dfs(vertex,vertex,frozenset({vertex}),(),Q(1))
    return tuple(found)

def cycles_satisfy(vertices: tuple[str, ...], edges: tuple[WeightedEdge, ...],
                   alpha: Q) -> bool:
    if not Q(0)<alpha<Q(1):
        raise ValueError("invalid alpha")
    return all(gain<=alpha**len(path) for path,gain in cycle_products(vertices,edges))

def bellman_potential(vertices: tuple[str, ...], edges: tuple[WeightedEdge, ...],
                      alpha: Q) -> dict[str,Q]:
    validate(vertices,edges)
    if not Q(0)<alpha<Q(1):
        raise ValueError("invalid alpha")
    result={v:Q(1) for v in vertices}
    for _ in range(len(vertices)-1):
        previous=result.copy()
        for e in edges:
            result[e.dst]=max(result[e.dst], previous[e.src]*e.rate/alpha)
    if not all(e.rate*result[e.src]<=alpha*result[e.dst] for e in edges):
        raise ValueError("violating graph cycle")
    return result

def path_products(vertices: tuple[str, ...], edges: tuple[WeightedEdge, ...],
                  start: str, names: tuple[str, ...]):
    validate(vertices,edges)
    index={e.name:e for e in edges}
    if start not in vertices: raise ValueError("bad start")
    current=start
    gain=Q(1)
    for name in names:
        edge=index[name]
        if edge.src!=current: raise ValueError("noncomposable path")
        gain*=edge.rate
        current=edge.dst
    return current,gain

def scaled_path_bound(weights: dict[str,Q],alpha:Q,start:str,end:str,length:int)->Q:
    if not weights or min(weights.values())<=0 or length<0 or not Q(0)<alpha<Q(1):
        raise ValueError("bad certificate")
    return weights[end]*alpha**length/weights[start]

def weighted_errors(rates:tuple[Q,...],errors:tuple[Q,...],initial:Q)->Q:
    if len(rates)!=len(errors) or any(x<0 for x in (*rates,*errors,initial)):
        raise ValueError("invalid weighted errors")
    output=initial
    for r,d in zip(rates,errors): output=r*output+d
    return output

def _product(xs)->Q:
    out=Q(1)
    for x in xs: out*=x
    return out

def explicit_error_sum(rates:tuple[Q,...],errors:tuple[Q,...],initial:Q)->Q:
    if len(rates)!=len(errors): raise ValueError("mismatched lengths")
    return initial*_product(rates)+sum((d*_product(rates[k+1:])
                                      for k,d in enumerate(errors)),Q(0))

def guard_locked(score:Q,normal_sq:Q,radius:Q)->bool:
    if normal_sq<=0 or radius<0: raise ValueError("bad hyperplane certificate")
    return score*score>normal_sq*radius*radius

def count_paths(vertices:tuple[str,...],edges:tuple[WeightedEdge,...],length:int)->int:
    validate(vertices,edges)
    if length<0: raise ValueError("negative length")
    counter={v:1 for v in vertices}
    for _ in range(length):
        next_counter={v:0 for v in vertices}
        for e in edges: next_counter[e.dst]+=counter[e.src]
        counter=next_counter
    return sum(counter.values())

def cover_certificate(vertices:tuple[str,...],edges:tuple[WeightedEdge,...],
                      weights:dict[str,Q],alpha:Q,length:int,diameter:Q)->tuple[int,Q]:
    """Number of length-k path images and uniform diameter upper bound."""
    if not weights or diameter<0 or min(weights.values())<=0:
        raise ValueError("bad geometry")
    return (count_paths(vertices,edges,length),
            diameter*alpha**length*max(weights.values())/min(weights.values()))
