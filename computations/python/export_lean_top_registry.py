#!/usr/bin/env python3
"""Generate shared literal top groups and complete faithful quotient kernels.

All inputs come from the committed binary menu.  Literal top subgroups are
shared across original pair frames.  Every generated cover is checked on
all original top-generator edges; every normal-registry edge and exact
kernel mask is then checked by Lean's kernel.  The Python enumeration is
only a witness producer, never a completeness premise.
"""
from pathlib import Path
import argparse, collections, gzip, json, sys
sys.dont_write_bytecode = True
from export_lean_menu_cayley import compose, table, lookup, checks, array, emit as emit_source
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedTopNormals'

def inverse(p): return tuple(p.index(i) for i in range(len(p)))
def unpack(c,w): return tuple(c//w**i%w for i in range(w))
def closure(gs,w):
    seen={tuple(range(w))};rows=list(seen)
    for x in rows:
        for g in gs:
            y=compose(x,g)
            if y not in seen:seen.add(y);rows.append(y)
    return tuple(sorted(seen))
def project(frame,g):
    loc={p:(i,b) for i,pair in enumerate(frame) for b,p in enumerate(pair)}
    result=tuple(loc[g[pair[0]-1]][0] for pair in frame)
    assert all(loc[g[pair[1]-1]][0]==result[i] for i,pair in enumerate(frame))
    return result

def words(gs,w):
    one=tuple(range(w));result={one:[]};todo=[one]
    for x in todo:
        for j,g in enumerate(gs):
            y=compose(x,g)
            if y not in result:result[y]=result[x]+[j];todo.append(y)
    return result

def context_bindings(g):
    shared=words(g['generators'],g['width']);result=[]
    for node,frame,pg in g['contexts']:
        original=words(pg,g['width'])
        result.append({'original_to_shared':[shared[x] for x in pg],
                       'shared_to_original':[original[x] for x in g['generators']]})
    return result

def finite_hom(gs,images,w,q):
    one=tuple(range(w));values={one:tuple(range(q))};rows=[one]
    for x in rows:
        for g,a in zip(gs,images):
            y=compose(x,g);b=compose(values[x],a)
            if y not in values:values[y]=b;rows.append(y)
            else:assert values[y]==b,'cover does not descend to actual Top'
    return values

def collect(pilot_group=None):
    groups={};contexts=[];wanted=None;pilot_key=None
    if pilot_group is not None:
        index=json.loads((OUT/'index.json').read_text())
        selected=[g for g in index if g['id']==pilot_group]
        if len(selected)!=1:raise ValueError(f'Unknown pilot top group {pilot_group}')
        saved=selected[0]
        wanted={(node,tuple(map(tuple,frame))) for node,frame,*_ in saved['contexts']}
        pilot_key=(saved['width'],tuple(sorted(map(tuple,saved['rows']))))
        wanted_nodes={node for node,_ in wanted}
    with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt') as f:
        meta=json.loads(next(f));nodes={n['id']:n for n in meta['nodes']}
        for line in f:
            rec=json.loads(line)
            if rec.get('kind')!='action':continue
            if wanted is not None and rec['id'] not in wanted_nodes:continue
            byframe=collections.defaultdict(list)
            for r in rec['normals']:
                if r['kind']=='pair':byframe[tuple(map(tuple,r['frame']))].append(r)
            for frame,pairs in sorted(byframe.items()):
                if wanted is not None and (rec['id'],frame) not in wanted:continue
                pg=tuple(project(frame,g) for g in nodes[rec['id']]['generators'])
                top=closure(pg,len(frame));key=(len(frame),top)
                if pilot_key is not None:assert key==pilot_key,'Pilot context changed literal top'
                state=groups.setdefault(key,{'tuples':set(),'covers':{},'contexts':[]})
                state['tuples'].add(pg);state['contexts'].append((rec['id'],frame,pg))
                for r in pairs:
                    t=closure(tuple(project(frame,g) for g in r['normal_generators']),len(frame))
                    old=state['covers'].get(t);q=r['cover_degree']
                    if old is not None and old['degree']<=q:continue
                    values=finite_hom(pg,[tuple(x-1 for x in g) for g in r['cover_images']],len(frame),q)
                    assert tuple(sorted(g for g,v in values.items() if v==tuple(range(q))))==t
                    state['covers'][t]={'degree':q,'values':values}
    result=[]
    for idx,((w,top),state) in enumerate(sorted(groups.items())):
        if pilot_group is not None:idx=pilot_group
        gens=min(state['tuples'],key=lambda g:(len(g),g));tab=table(gens,w)
        rows=[unpack(c,w) for c in tab['codes']];ri={x:i for i,x in enumerate(rows)}
        normals=sorted(state['covers'],key=lambda t:(len(t),t));ni={frozenset(t):i for i,t in enumerate(normals)}
        cases=[]
        for t in normals:
            ts=set(t);children=[]
            for x in rows:
                central=x not in ts and compose(x,x) in ts and all(compose(compose(x,g),inverse(compose(g,x))) in ts for g in gens)
                if central:
                    enlarged=frozenset(ts|{compose(x,y) for y in ts})
                    assert enlarged in ni,'missing actual central-involution child'
                    children.append(ni[enlarged])
                else:children.append(0)
            c=state['covers'][t];vals=[c['values'][x] for x in rows]
            cases.append({'normal':t,'mask':sum(1<<ri[x] for x in t),'degree':c['degree'],
                          'values':vals,'images':[c['values'][g] for g in gens],'child':children})
        result.append({'id':idx,'width':w,'rows':rows,'generators':gens,'table':tab,'cases':cases,'contexts':state['contexts']})
    if pilot_group is not None:
        assert len(result)==1,'Pilot must contain exactly one literal top'
        assert {(node,frame) for node,frame,_ in result[0]['contexts']}==wanted,'Missing pilot contexts'
    return result

def source(g):
    idx=g['id'];label=f'Top{idx:03d}';node={'id':'b'+label,'degree':g['width'],'generators':[[x+1 for x in p] for p in g['generators']]}
    _,text=emit_source(node)
    text=text.replace('BinaryMenuCayley'+label,'BinaryTopSource'+f'{idx:03d}')
    text=text.replace('private def prevRow','def prevRow').replace('private theorem prev_checked','theorem prev_checked')
    text=text.replace('Generated from the original menu permutations by export_lean_menu_cayley.py.','Generated from actual projected menu permutations by export_lean_top_registry.py.')
    return f'Source{idx:03d}.lean',text

def state_parts(g):
    idx=g['id'];tag=f'{idx:03d}';src=f'BinaryTopSource{tag}';n=len(g['rows']);d=len(g['generators']);m=len(g['cases'])
    s=f'''import SymmetricSubgroupAsymptotics.BinaryTopNormalRegistry
import SymmetricSubgroupAsymptotics.BinaryTopNumericTests
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.Source{tag}

/-! Complete exact normal kernels and faithful quotient covers of literal
shared top group {tag}. Generated by export_lean_top_registry.py. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTopRegistry{tag}
abbrev Source := FiniteGroupRow {n}
local instance : Group Source := {src}.group

def generators (j : Fin {d}) : Source :=
  ⟨{src}.certificate.next {src}.certificate.identity j⟩

'''
    for i,c in enumerate(g['cases']):
        q=c['degree'];vals=c['values'];ivs=[inverse(x) for x in vals]
        if q:
            vf=f'({lookup([array(x) for x in vals],"i.val")} : Array (Fin {q}))[x.val]!'
            vi=f'({lookup([array(x) for x in ivs],"i.val")} : Array (Fin {q}))[x.val]!'
        else:vf=vi='Fin.elim0 x'
        gi=[g['rows'].index(x) for x in g['generators']]
        s+=f'''namespace N{i}
def values (i : Fin {n}) : Equiv.Perm (Fin {q}) where
  toFun x := {vf}
  invFun x := {vi}
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def images (j : Fin {d}) : Equiv.Perm (Fin {q}) :=
  values ({lookup(gi,'j.val')} : Fin {n})

private theorem step_checked : ∀ i j,
    values ({src}.certificate.next i j)=values i*images j := {checks(n)}
private theorem identity_checked : values {src}.certificate.identity=1 := by decide +kernel

def hom : Source →* Equiv.Perm (Fin {q}) :=
  {src}.certificate.checkedHom values images step_checked
    {src}.rows_injective {src}.prevRow {src}.prev_checked identity_checked

def mask (x : Source) : Bool := Nat.testBit {c['mask']} x.index.val

private theorem mask_checked : ∀ i : Fin {n}, mask ⟨i⟩=true ↔ values i=1 := {checks(n)}

def state : BinaryTopKernelData Source where
  degree := {q}
  hom := hom
  mask := mask
  mask_eq x := mask_checked x.index

theorem state_hom_apply (x : Source) : state.hom x=values x.index := rfl

theorem size_checked : state.size={len(c['normal'])} := by
  unfold BinaryTopKernelData.size
  decide +kernel

end N{i}

'''
    s+=f'''def states (i : Fin {m}) : BinaryTopKernelData Source :=
  {lookup([f'N{i}.state' for i in range(m)])}

def sizes (i : Fin {m}) : ℕ :=
  {lookup([len(c['normal']) for c in g['cases']])}

theorem states_size (i : Fin {m}) : (states i).size=sizes i := by
  fin_cases i
'''
    for i in range(m):s+=f'  · exact N{i}.size_checked\n'
    s+='\n'
    edgeparts=[]
    for i,c in enumerate(g['cases']):
        q=c['degree']
        edgeparts.append(f'''private def child{i} (x : Source) : Fin {m} :=
  {lookup(c['child'],'x.index.val')}

private theorem edges{i} : ∀ x : Source,
    N{i}.state.liftTests generators x →
    (∀ y, N{i}.mask y=true → (states (child{i} x)).mask y=true) ∧
    (states (child{i} x)).mask x=true ∧
    (states (child{i} x)).size=N{i}.state.size*2 := by
  have checked : ∀ x : Fin {n},
      (N{i}.values x≠(1 : Equiv.Perm (Fin {q})) ∧
        N{i}.values x*N{i}.values x=1 ∧
        ∀ j : Fin {d}, N{i}.values x*N{i}.values (generators j).index=
          N{i}.values (generators j).index*N{i}.values x) →
      (∀ y : Fin {n}, N{i}.mask ⟨y⟩=true → (states (child{i} ⟨x⟩)).mask ⟨y⟩=true) ∧
      (states (child{i} ⟨x⟩)).mask ⟨x⟩=true ∧
      (states (child{i} ⟨x⟩)).size=N{i}.state.size*2 := by
    simp only [states_size,N{i}.size_checked]
    decide +kernel
  intro x hx
  have ht := (N{i}.state.liftTests_iff_hom generators x).mp hx
  simp only [N{i}.state_hom_apply] at ht
  have hc := checked x.index ht
  exact ⟨fun y hy => hc.1 y.index hy,hc.2⟩

''')
    tail=f'''private def child (i : Fin {m}) : Source → Fin {m} :=
  {lookup([f'child{i}' for i in range(m)])}

def registry : BinaryTopNormalRegistry generators states where
  bottom := 0
  bottom_mask := by decide +kernel
  child := child
  parent_mem := by
    intro i
    fin_cases i
'''
    for i in range(m):tail+=f'    · exact fun x hx => (edges{i} x hx).1\n'
    tail+='''  lift_mem := by
    intro i
    fin_cases i
'''
    for i in range(m):tail+=f'    · exact fun x hx => (edges{i} x hx).2.1\n'
    tail+='''  child_size := by
    intro i
    fin_cases i
'''
    for i in range(m):tail+=f'    · exact fun x hx => (edges{i} x hx).2.2\n'
    tail+=f'''
theorem isPGroup : IsPGroup 2 Source :=
  IsPGroup.of_card (n := {n.bit_length()-1}) (by rw [Nat.card_eq_fintype_card]; rfl)

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, (states i).kernel=N := registry.complete isPGroup N

/-- Completeness on the original literal permutation top, without an
abstract isomorphism replacing its action. -/
def originalStates (i : Fin {m}) : BinaryTopKernelData
    (Subgroup.closure (Set.range {src}.generators)) :=
  (states i).transport {src}.originalEquiv

theorem complete_original
    (N : Subgroup (Subgroup.closure (Set.range {src}.generators))) [N.Normal] :
    ∃ i, (originalStates i).kernel=N := by
  obtain ⟨i,hi⟩ := registry.complete_map_of_equiv isPGroup {src}.originalEquiv N
  exact ⟨i,((states i).transport_kernel {src}.originalEquiv).trans hi⟩

end SymmetricSubgroupAsymptotics.BinaryTopRegistry{tag}
'''
    return s,edgeparts,tail

def state_module(g):
    head,edges,tail=state_parts(g)
    return f'Registry{g["id"]:03d}.lean',head+''.join(edges)+tail

def pilot_modules(g):
    """Separate exact source, quotient states, individual edges, and assembly."""
    tag=f'{g["id"]:03d}';head,edges,tail=state_parts(g)
    namespace=f'SymmetricSubgroupAsymptotics.BinaryTopRegistry{tag}'
    head=head.replace(f'.GeneratedTopNormals.Source{tag}',f'.GeneratedTopNormals.PilotSource{tag}')
    outputs=[(f'PilotStates{tag}.lean',head+f'end {namespace}\n')]
    def options(instance_name):
        return f'''set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
noncomputable section
namespace {namespace}
local instance {instance_name} : Group Source := BinaryTopSource{tag}.group

'''
    imports=[]
    for i,edge in enumerate(edges):
        name=f'PilotEdges{tag}_{i:03d}'
        imports.append(f'import SymmetricSubgroupAsymptotics.GeneratedTopNormals.{name}\n')
        edge=edge.replace(f'private def child{i} ',f'def child{i} ').replace(f'private theorem edges{i} ',f'theorem edges{i} ')
        body=f'import SymmetricSubgroupAsymptotics.GeneratedTopNormals.PilotStates{tag}\n\n'+options(f'pilotEdge{i:03d}Group')+edge+f'end {namespace}\n'
        outputs.append((name+'.lean',body))
    outputs.append((f'Pilot{tag}.lean',''.join(imports)+'\n'+options('pilotAggregateGroup')+tail))
    return outputs

def all_module(gs):
    s=''.join(f'import SymmetricSubgroupAsymptotics.GeneratedTopNormals.Batch{i:03d}\n' for i in range((len(gs)+9)//10))
    s+='\n/-! Every shared literal top-normal registry, with actual quotient covers. -/\nset_option autoImplicit false\nnoncomputable section\nnamespace SymmetricSubgroupAsymptotics.BinarySharedTopRegistry\n'
    for g in gs:
        tag=f'{g["id"]:03d}'
        s+=f'''
private def group{tag} : BinaryCompleteTopRegistry where
  width := {g['width']}
  top := Subgroup.closure (Set.range BinaryTopSource{tag}.generators)
  count := {len(g['cases'])}
  states := BinaryTopRegistry{tag}.originalStates
  complete N hN := by
    letI := hN
    exact BinaryTopRegistry{tag}.complete_original N
'''
    s+=f'\ndef catalogue (i : Fin {len(gs)}) : BinaryCompleteTopRegistry :=\n  '+lookup([f'group{g["id"]:03d}' for g in gs])+'\n'
    s+='\nend SymmetricSubgroupAsymptotics.BinarySharedTopRegistry\n'
    return 'All.lean',s

def combined_module(gs,name):
    s='import SymmetricSubgroupAsymptotics.BinaryTopNormalRegistry\nimport SymmetricSubgroupAsymptotics.BinaryTopNumericTests\nimport SymmetricSubgroupAsymptotics.FinitePermutationEncoding\nimport Mathlib.Order.Fin.Basic\n'
    for g in gs:
        for _,body in [source(g),state_module(g)]:
            s+='\n'+'\n'.join(line for line in body.splitlines() if not line.startswith('import '))+'\n'
    return name,s

def batch_module(gs,batch):
    return combined_module(gs[10*batch:10*(batch+1)],f'Batch{batch:03d}.lean')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true')
    selection=ap.add_mutually_exclusive_group()
    selection.add_argument('--group',type=int,action='append')
    selection.add_argument('--pilot-group',type=int,help='Use the existing index to collect and emit one literal top as PilotNNN; preserve canonical files and index.')
    ap.add_argument('--source-only',action='store_true',help='With --pilot-group, emit only PilotSourceNNN to isolate source checks.')
    args=ap.parse_args()
    if args.source_only and args.pilot_group is None:ap.error('--source-only requires --pilot-group')
    gs=collect(args.pilot_group)
    OUT.mkdir(exist_ok=True)
    if args.pilot_group is not None:
        tag=f'{args.pilot_group:03d}'
        outputs=[(f'PilotSource{tag}.lean',source(gs[0])[1])]
        if not args.source_only:
            outputs.extend(pilot_modules(gs[0]))
        for name,s in outputs:
            p=OUT/name;b=s.encode()
            if args.check:
                if not p.is_file() or p.read_bytes()!=b:raise SystemExit(f'Stale generated source {p}')
            elif not p.is_file() or p.read_bytes()!=b:p.write_bytes(b)
            print(name,len(b),flush=True)
        return
    selected=gs if args.group is None else [gs[i] for i in args.group]
    batches=sorted({g['id']//10 for g in selected})
    for batch in batches:
        outputs=[batch_module(gs,batch)]
        for g in gs[10*batch:10*(batch+1)]:
            for prefix in ['Source','Registry']:
                outputs.append((f'{prefix}{g["id"]:03d}.lean',f'import SymmetricSubgroupAsymptotics.GeneratedTopNormals.Batch{batch:03d}\n'))
        for name,s in outputs:
            p=OUT/name;b=s.encode()
            if args.check:
                if not p.is_file() or p.read_bytes()!=b:raise SystemExit(f'Stale generated source {p}')
            elif not p.is_file() or p.read_bytes()!=b:p.write_bytes(b)
            print(name,len(b),flush=True)
    name,s=all_module(gs);p=OUT/name;b=s.encode()
    if args.check:
        if not p.is_file() or p.read_bytes()!=b:raise SystemExit(f'Stale generated source {p}')
    elif not p.is_file() or p.read_bytes()!=b:p.write_bytes(b)
    index=[{'id':g['id'],'batch':g['id']//10,'width':g['width'],'order':len(g['rows']),'normal_count':len(g['cases']),
            'generators':g['generators'],'rows':g['rows'],'normals':[c['normal'] for c in g['cases']],
            'degrees':[c['degree'] for c in g['cases']],'contexts':g['contexts'],'bindings':context_bindings(g)} for g in gs]
    p=OUT/'index.json';b=(json.dumps(index,separators=(',',':'))+'\n').encode()
    if args.check:
        if not p.is_file() or p.read_bytes()!=b:raise SystemExit(f'Stale generated index {p}')
    elif not p.is_file() or p.read_bytes()!=b:p.write_bytes(b)
    print(json.dumps({'groups':len(gs),'normal_states':sum(len(g['cases']) for g in gs),'frames':sum(len(g['contexts']) for g in gs)}))
if __name__=='__main__':main()
