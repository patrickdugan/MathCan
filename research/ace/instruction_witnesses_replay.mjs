// ACE-03V. Independent pinned-entry packing and finite assembly replay.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildInstructionWitnesses } from './instruction_witnesses.mjs';
import { expectedFiniteSelection } from './finite_witness_selection_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedInstructionWitnesses(defs) {
  const A=p=>['A',p],E=p=>['E',p],I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q],O=(p,q)=>['|',p,q],M=(i,j)=>['M',i,j];
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const form=(name,...args)=>embed(defs[name],args),inc=(xs,d)=>xs.map(i=>i+d);
  const Pair=(p,x,y)=>form('pair',p,x,y),Val=(f,k,r)=>form('val',f,k,r);
  const Binary=(c,tag,i,j)=>E(C(Pair(0,i+1,j+1),Pair(c+1,tag+1,0)));
  function Witness(c,f,k,r,n,a,tags) {
    const arms=[];
    for(let op=0;op<5;op++) {
      if(op===2) {
        const sem=E(C(Val(f+2,1,0),form('relNeg',r+2,0,n+2,a+2)));
        arms.push(E(C(M(0,k+1),C(Pair(c+1,tags[op]+1,0),sem))));
        continue;
      }
      let semantic;
      if(op<2)semantic=form(op===0?'relEq':'relMem',r+2,n+2,a+2,1,0);
      else if(op===3)semantic=E(E(C(C(Val(f+4,3,1),Val(f+4,2,0)),form('relAnd',r+4,1,0))));
      else semantic=E(C(Val(f+3,2,0),form('relEx',r+3,0,n+3,a+3,1)));
      const first=op<2?n:k,second=op===3?k:n;
      arms.push(E(C(M(0,first+1),E(C(M(0,second+2),C(Binary(c+2,tags[op]+2,1,0),semantic))))));
    }
    return arms.reduce(O);
  }
  const Candidate=(k,c,f,n,a,tags)=>E(C(Val(f+1,k+1,0),Witness(c+1,f+1,k+1,0,n+1,a+1,inc(tags,1))));
  const Tagged=(g,f,m,n,a,tags)=>C(form('graph',g,m),A(I(M(0,m+1),A(I(Val(g+2,1,0),Candidate(1,0,f+2,n+2,a+2,inc(tags,2)))))));
  const all=(n,p)=>n?A(all(n-1,p)):p,tags=[4,3,2,1,0];
  const formulas={
    binary_code:Binary(0,1,2,3),
    instruction_witness:Witness(0,1,2,3,4,5,[6,7,8,9,10]),
    candidate:Candidate(0,1,2,3,4,[5,6,7,8,9]),
    tagged_program:Tagged(0,1,2,3,4,[5,6,7,8,9])
  };
  const proofs={
    binary_instruction_code_exists:all(3,E(Binary(0,3,2,1))),
    entry_has_tagged_instruction:all(10,I(form('entry',9,8,7,6,5),E(Witness(0,10,9,8,7,6,inc(tags,1))))),
    tagged_instruction_has_entry:all(11,I(Witness(10,9,8,7,6,5,tags),form('entry',9,8,7,6,5))),
    valid_program_candidate_total:all(9,I(form('validProgram',8,7,6,5),A(I(M(0,8),E(Candidate(1,0,10,8,7,inc(tags,2)))))))
  };
  for(const [name,p] of Object.entries(expectedFiniteSelection(defs,formulas.candidate,8)))proofs['instruction_'+name]=p;
  proofs.finite_valid_program_tagged_graph=all(10,I(form('omega',9),I(M(7,9),I(form('validProgram',8,7,6,5),E(Tagged(0,9,8,7,6,inc(tags,1)))))));
  return {formulas,proofs};
}

function runInstructionWitnesses() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildInstructionWitnesses(defs),expected=expectedInstructionWitnesses(defs);
  if(!same(built.formulas,expected.formulas)||!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('instruction independent interface');
  const checks=[],controls=[],axioms=new Map();
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(p,want){const got=kernel(0,[],p,false,'ZF');if(!same(got.goal,want))throw Error('instruction goal mismatch');}
  for(const [name,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[name]))throw Error('independent instruction theorem '+name);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[name]))throw Error('kernel instruction theorem');
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(x=>!['pairing','union','foundation','separation'].includes(x)))throw Error('unexpected instruction axiom');
    checks.push({id:name,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    let p0=p.proof;
    while(p0[0]==='uI')p0=p0[1];
    reject(name+':drop_binders',()=>kernel(0,[],p0,false,'ZF'));
    if(used.size)reject(name+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
  }
  const logicChecks=[];
  for(const name of ['tagged_instruction_has_entry','instruction_empty_domain_selection']) {
    const got=kernel(0,[],built.proofs[name].proof,false,'logic');
    if(!same(got.goal,expected.proofs[name]))throw Error('pure logical instruction check');
    logicChecks.push(name);
  }
  for(const [label,index] of [['omega',0],['finite_membership',1],['valid_program',2]]) {
    const changed=structuredClone(expected.proofs.finite_valid_program_tagged_graph);
    let p=changed;
    for(let i=0;i<10;i++)p=p[1];
    for(let i=0;i<index;i++)p=p[2];
    p.splice(0,p.length,...p[2]);
    reject('finite_assembly:omit_'+label,()=>exact(built.proofs.finite_valid_program_tagged_graph.proof,changed));
  }
  function removeArm(tree,index,count) {
    if(count===2)return tree[index===0?2:1];
    if(index===count-1)return tree[1];
    return ['|',removeArm(tree[1],index,count-1),tree[2]];
  }
  for(let op=0;op<5;op++) {
    const changed=structuredClone(expected.proofs.entry_has_tagged_instruction);
    let p=changed;
    for(let i=0;i<10;i++)p=p[1];
    p[2][1]=removeArm(p[2][1],op,5);
    reject('entry_packing:omit_opcode_'+op,()=>exact(built.proofs.entry_has_tagged_instruction.proof,changed));
  }
  const missingEntry=structuredClone(expected.proofs.entry_has_tagged_instruction);
  let endpoint=missingEntry;
  for(let i=0;i<10;i++)endpoint=endpoint[1];
  endpoint.splice(0,endpoint.length,...endpoint[2]);
  reject('entry_packing:omit_entry_premise',()=>exact(built.proofs.entry_has_tagged_instruction.proof,missingEntry));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {
    experiment:'ACE-03V',part:'pinned_entry_tagged_witnesses_and_finite_assembly',checks,
    checked_modules:checks.length,kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    pure_logic_checks:logicChecks,negative_controls:controls.length,controls,
    formula_argument_orders:{binary_code:['c','tag','i','j'],instruction_witness:['c','f','k','r','n','A','tag0','tag1','tag2','tag3','tag4'],
      candidate:['k','c','f','n','A','tag0','tag1','tag2','tag3','tag4'],tagged_program:['g','f','m','n','A','tag0','tag1','tag2','tag3','tag4']},
    main_quantifier_order:['w','f','m','n','A','tag0','tag1','tag2','tag3','tag4'],
    main_premises:['Omega(w)','m in w','validProgram(f,m,n,A)'],
    tag_distinctness_required:false,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'exact pinned-entry packing and finite tagged-program existence under supplied omega and finite-domain premises; tags may coincide',
    downstream_requirements:['distinct tags for unique opcode decoding','exact five-field decoding','natural-number program coding','execution existence and internal constructibility']
  };
}

export { expectedInstructionWitnesses, runInstructionWitnesses };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runInstructionWitnesses(),null,2));
