// ACE-01: finite witness compilation and independent certificate replay.
// Run: node research/ace/finite_choice.mjs
function exactKeys(o, keys) {
  return o !== null && typeof o === "object" && !Array.isArray(o) &&
    Object.keys(o).sort().join("|") === [...keys].sort().join("|");
}

function validInstance(x) {
  if (!exactKeys(x, ["id","width","rows"]) || typeof x.id !== "string" || !x.id ||
      !Number.isSafeInteger(x.width) || x.width < 0 || !Array.isArray(x.rows)) return false;
  for (let i=0; i<x.rows.length; i++) {
    const row=x.rows[i];
    if (!Array.isArray(row) || row.length !== x.width) return false;
    for (let j=0; j<row.length; j++) if (row[j] !== 0 && row[j] !== 1) return false;
  }
  return true;
}

function scan(x) {
  let probes=0; const witnesses=[];
  for (const row of x.rows) {
    let found=-1;
    for (let j=0; j<x.width; j++) {
      probes++;
      if (row[j]===1) { found=j; break; }
    }
    if (found<0) return {ok:false,probes,witnesses:null};
    witnesses.push(found);
  }
  return {ok:true,probes,witnesses};
}

function checkSource(x,p) {
  if (!validInstance(x) || !exactKeys(p,["kind","instance_id"]) ||
      p.kind!=="finite_choice_macro_v1" || p.instance_id!==x.id) return {ok:false,probes:0};
  const s=scan(x);
  return {ok:s.ok,probes:s.probes};
}

function checkTarget(x,p) {
  if (!validInstance(x) || !exactKeys(p,["kind","instance_id","witnesses"]) ||
      p.kind!=="explicit_witness_v1" || p.instance_id!==x.id ||
      !Array.isArray(p.witnesses) || p.witnesses.length!==x.rows.length) return {ok:false,probes:0};
  let probes=0;
  for (let i=0;i<x.rows.length;i++) {
    const j=p.witnesses[i];
    if (!Number.isSafeInteger(j) || j<0 || j>=x.width) return {ok:false,probes};
    probes++;
    if (x.rows[i][j]!==1) return {ok:false,probes};
  }
  return {ok:true,probes};
}

function compile(x,p) {
  const source=checkSource(x,p);
  if (!source.ok) return {certificate:null,source_probes:source.probes,search_probes:0};
  const s=scan(x);
  if (!s.ok) throw Error("source/search inconsistency");
  return {certificate:{kind:"explicit_witness_v1",instance_id:x.id,witnesses:s.witnesses},
    source_probes:source.probes,search_probes:s.probes};
}

function insist(b,msg) { if (!b) throw Error(msg); }

function newStats() {
  return {instances:0,satisfiable:0,unsatisfiable:0,accepted_targets:0,rejected_sources:0,
    negative_controls:0,source_probes:0,search_probes:0,target_probes:0};
}

function trial(x,expected,stats) {
  const p={kind:"finite_choice_macro_v1",instance_id:x.id};
  const result=compile(x,p);
  stats.instances++;
  stats.source_probes+=result.source_probes;
  stats.search_probes+=result.search_probes;
  insist(Boolean(result.certificate)===expected,`wrong compilation ${x.id}`);
  if (expected) {
    stats.satisfiable++;
    const c=result.certificate, checked=checkTarget(x,c);
    insist(checked.ok,`bad target ${x.id}`);
    stats.accepted_targets++;
    stats.target_probes+=checked.probes;
    const bad=[
      {...c,instance_id:x.id+"-foreign"},
      {...c,kind:"global_choice"},
      {...c,witnesses:[...c.witnesses,0]},
      {...c,extra:true}
    ];
    if (x.rows.length) {
      for (const wrong of [-1,x.width,"0",0.5,null]) {
        const w=[...c.witnesses]; w[0]=wrong; bad.push({...c,witnesses:w});
      }
      bad.push({...c,witnesses:c.witnesses.slice(1)});
      const i=x.rows.findIndex(r=>r.includes(0));
      if (i>=0) {
        const w=[...c.witnesses]; w[i]=x.rows[i].indexOf(0); bad.push({...c,witnesses:w});
      }
    }
    for (const q of bad) {
      insist(!checkTarget(x,q).ok,`accepted corrupt target ${x.id}`);
      stats.negative_controls++;
    }
  } else {
    stats.unsatisfiable++;
    stats.rejected_sources++;
    insist(!checkTarget(x,{kind:"explicit_witness_v1",instance_id:x.id,
      witnesses:Array(x.rows.length).fill(0)}).ok,`accepted false goal ${x.id}`);
    stats.negative_controls++;
  }
  for (const q of [{...p,kind:"global_choice"},{...p,instance_id:x.id+"-foreign"}]) {
    insist(!checkSource(x,q).ok,`accepted corrupt source ${x.id}`);
    stats.negative_controls++;
  }
}

function rng(seed) {
  let s=seed>>>0;
  return () => {s^=s<<13;s^=s>>>17;s^=s<<5;return s>>>0;};
}

function run() {
  const exhaustive=newStats();
  for (let n=0;n<=3;n++) for (let m=0;m<=3;m++) {
    for (let mask=0;mask<2**(n*m);mask++) {
      const rows=Array.from({length:n},(_,i)=>Array.from({length:m},(_,j)=>(mask>>(i*m+j))&1));
      const rowMask=(1<<m)-1;
      let expected=true;
      for(let i=0;i<n;i++) if (((mask>>(i*m))&rowMask)===0) expected=false;
      trial({id:`E-${n}-${m}-${mask}`,width:m,rows},expected,exhaustive);
    }
  }
  const stress={};
  for (const seed of [109,113,127]) {
    const next=rng(seed), s=newStats();
    for(let k=0;k<64;k++) {
      const n=4+next()%61,m=2+next()%31;
      const rows=Array.from({length:n},(_,i)=>{
        const r=Array.from({length:m},()=>next()%8===0?1:0);
        if(k%3===0){r.fill(0);r[m-1]=1;}
        else r[next()%m]=1;
        return r;
      });
      const expected=k%4!==0;
      if(!expected) rows[next()%n].fill(0);
      trial({id:`S-${seed}-${k}`,width:m,rows},expected,s);
    }
    stress[seed]=s;
  }
  const malformed=[null,{id:"a",width:1,rows:[[true]]},{id:"a",width:2,rows:[[1]]},
    {id:"a",width:1,rows:[Array(1)]},{id:"a",width:-1,rows:[]},
    {id:"a",width:1,rows:Array(1)}];
  for (const x of malformed) {
    insist(!checkSource(x,{kind:"finite_choice_macro_v1",instance_id:"a"}).ok,"bad instance source");
    insist(!checkTarget(x,{kind:"explicit_witness_v1",instance_id:"a",witnesses:[]}).ok,"bad instance target");
  }
  return {experiment:"ACE-01",scope:"synthetic finite relation; not ZF/ZFC",exhaustive,stress,
    malformed_instance_rejections:malformed.length*2,
    accounting:"relation-validation overhead excluded from predicate probes; source and search charged separately"};
}

export { checkSource, checkTarget, compile, run };
console.log(JSON.stringify(run(), null, 2));
