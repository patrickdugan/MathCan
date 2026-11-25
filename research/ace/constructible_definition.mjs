// Parameter-free class definition generator; generated AST is in de Bruijn form.
function definition(prefix="v"){
  let serial=0;
  const Q=(a,b)=>["=",a,b],M=(a,b)=>["M",a,b],F=["F"],I=(p,q)=>[">",p,q],C=(...p)=>p.reduce((a,b)=>["&",a,b]),O=(...p)=>p.reduce((a,b)=>["|",a,b]),N=p=>I(p,F),B=(p,q)=>C(I(p,q),I(q,p));
  const bind=(op,body)=>{const v=prefix+(serial++);return [op,v,body(v)];};
  const A=f=>bind("A",f),E=f=>bind("E",f);
  const all=(a,f)=>A(x=>I(M(x,a),f(x))),some=(a,f)=>E(x=>C(M(x,a),f(x)));
  const empty=a=>A(x=>N(M(x,a)));
  const subset=(a,b)=>all(a,x=>M(x,b));
  const trans=a=>all(a,x=>subset(x,a));
  const ord=a=>C(trans(a),all(a,trans));
  const succ=(a,b)=>A(x=>B(M(x,b),O(M(x,a),Q(x,a))));
  const ind=a=>C(some(a,empty),all(a,x=>some(a,y=>succ(x,y))));
  const omega=a=>C(ind(a),A(b=>I(ind(b),subset(a,b))));
  const singleton=(p,a)=>A(x=>B(M(x,p),Q(x,a)));
  const unordered=(p,a,b)=>A(x=>B(M(x,p),O(Q(x,a),Q(x,b))));
  const pair=(p,a,b)=>E(u=>E(v=>C(singleton(u,a),unordered(v,a,b),unordered(p,u,v))));
  const val=(f,i,y)=>some(f,p=>pair(p,i,y));
  const uniqueValue=(f,i)=>E(y=>C(val(f,i,y),A(z=>I(val(f,i,z),Q(z,y)))));
  const graph=(f,d)=>C(all(f,p=>some(d,i=>E(y=>pair(p,i,y)))),all(d,i=>uniqueValue(f,i)));
  const tuple=(s,n,a)=>C(graph(s,n),all(n,i=>some(a,y=>val(s,i,y))));
  const agree=(s,t,n,i)=>all(n,j=>I(N(Q(i,j)),A(x=>B(val(s,j,x),val(t,j,x)))));
  const relAtom=(r,n,a,i,j,op)=>A(s=>{
    const property=some(a,x=>some(a,y=>C(val(s,i,x),val(s,j,y),op(x,y))));
    return B(M(s,r),C(tuple(s,n,a),property));
  });
  const relNeg=(r,p,n,a)=>A(s=>B(M(s,r),C(tuple(s,n,a),N(M(s,p)))));
  const relAnd=(r,p,q)=>A(s=>B(M(s,r),C(M(s,p),M(s,q))));
  const relEx=(r,p,n,a,i)=>A(s=>B(M(s,r),C(tuple(s,n,a),some(p,t=>agree(s,t,n,i)))));
  const entry=(f,k,r,n,a)=>O(
    some(n,i=>some(n,j=>relAtom(r,n,a,i,j,Q))),
    some(n,i=>some(n,j=>relAtom(r,n,a,i,j,M))),
    some(k,i=>E(p=>C(val(f,i,p),relNeg(r,p,n,a)))),
    some(k,i=>some(k,j=>E(p=>E(q=>C(val(f,i,p),val(f,j,q),relAnd(r,p,q)))))),
    some(k,i=>some(n,j=>E(p=>C(val(f,i,p),relEx(r,p,n,a,j)))))
  );
  const slice=(x,r,a,n,z,b)=>A(y=>{
    const witness=some(r,s=>C(val(s,z,y),agree(s,b,n,z)));
    return B(M(y,x),C(M(y,a),witness));
  });
  const lastSlice=(f,m,n,a,x)=>some(m,k=>C(succ(k,m),E(r=>{
    const atZero=some(n,z=>C(empty(z),E(b=>C(tuple(b,n,a),slice(x,r,a,n,z,b)))));
    return C(val(f,k,r),atZero);
  })));
  const validProgram=(f,m,n,a)=>C(graph(f,m),all(m,k=>E(r=>C(val(f,k,r),entry(f,k,r,n,a)))));
  const nonempty=a=>E(i=>M(i,a));
  const definable=(a,x)=>O(empty(x),E(w=>{
    const program=some(w,n=>some(w,m=>C(nonempty(n),nonempty(m),
      E(f=>C(validProgram(f,m,n,a),lastSlice(f,m,n,a,x))))));
    return C(omega(w),program);
  }));
  const defSet=(a,b)=>A(x=>B(M(x,b),definable(a,x)));
  const limit=b=>N(some(b,a=>succ(a,b)));
  const limitStage=(f,b,r)=>A(x=>B(M(x,r),some(b,i=>E(s=>C(val(f,i,s),M(x,s))))));
  const successorStage=(f,b,r)=>some(b,i=>C(succ(i,b),E(s=>C(val(f,i,s),defSet(s,r)))));
  const stage=(f,b,r)=>O(successorStage(f,b,r),C(limit(b),limitStage(f,b,r)));
  const stageGraph=(f,d)=>C(graph(f,d),all(d,b=>E(r=>C(val(f,b,r),stage(f,b,r)))));
  const l=x=>E(alpha=>C(ord(alpha),E(d=>C(succ(alpha,d),E(f=>{
    const witness=E(r=>C(val(f,alpha,r),M(x,r)));
    return C(stageGraph(f,d),witness);
  })))));
  const compile=(p,env)=>{
    const [op,a,b]=p;
    if(op==="F")return F;
    if(op==="A"||op==="E")return [op,compile(b,[a,...env])];
    if(op==="M"||op==="="){
      const i=env.indexOf(a),j=env.indexOf(b);if(i<0||j<0)throw Error("free variable");
      return [op,i,j];
    }
    return [op,compile(a,env),compile(b,env)];
  };
  const free=["arg0","arg1","arg2"];
  return {
    empty:compile(empty(free[0]),[free[0]]),
    ordinal:compile(ord(free[0]),[free[0]]),
    successor:compile(succ(free[0],free[1]),free.slice(0,2)),
    pair:compile(pair(free[0],free[1],free[2]),free),
    omega:compile(omega(free[0]),[free[0]]),
    graph:compile(graph(free[0],free[1]),free.slice(0,2)),
    definable:compile(definable(free[0],free[1]),free.slice(0,2)),
    Def:compile(defSet(free[0],free[1]),free.slice(0,2)),
    L:compile(l(free[0]),[free[0]])
  };
}

export { definition };
