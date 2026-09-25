#!/usr/bin/env python3
"""Export complete shared invariant-axis registries of literal binary pair kernels.

Every subspace has a reversible F2 coordinate chart. Actual top-generator
stability and local normal-orbit join witnesses are checked in Lean; the
normal-lift list is not a completeness premise. Run export_lean_top_registry
first to install the shared original top sources and index.
"""
import argparse,gzip,json
from pathlib import Path
from export_lean_menu_cayley import ROOT,lookup
OUT=ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedKernelAxes'

def basis(xs):
 b={}
 for x in xs:
  for i in sorted(b,reverse=True):x=min(x,x^b[i])
  if x:
   i=x.bit_length()-1
   for j in list(b):b[j]=min(b[j],b[j]^x)
   b[i]=x
 return tuple(sorted(b.values()))
def span(b):
 s={0}
 for v in b:s|={x^v for x in s}
 return frozenset(s)
def act(p,v):return sum(((v>>i)&1)<<j for i,j in enumerate(p))
def submodules(k,top):
 orbitspaces=set(basis(act(t,v) for t in top) for v in span(k));seen={()};todo=[()]
 for a in todo:
  sa=span(a)
  for v in orbitspaces:
   if all(x in sa for x in v):continue
   b=basis(a+v)
   if b not in seen:seen.add(b);todo.append(b)
 return sorted(todo,key=lambda a:(len(a),a))
def vector(b,code):
 v=0
 for i,x in enumerate(b):
  if code>>i&1:v^=x
 return v
def decompose(pool,x):
 b={}
 for j,y in enumerate(pool):
  m=1<<j
  for p in sorted(b,reverse=True):
   if y>>p&1:y^=b[p][0];m^=b[p][1]
  if y:b[y.bit_length()-1]=(y,m)
 m=0
 for p in sorted(b,reverse=True):
  if x>>p&1:x^=b[p][0];m^=b[p][1]
 assert not x
 return m

def inventory():
 tops=json.loads((ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedTopNormals/index.json').read_text())
 with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt') as f:
  next(f);records={r['id']:r for line in f if (r:=json.loads(line)).get('kind')=='action'}
 modules={}
 for t in tops:
  for node,frame,images in t['contexts']:
   rec=next(r for r in records[node]['normals'] if r['kind']=='pair' and r['frame']==frame)
   pos={p:(i,b) for i,pair in enumerate(frame) for b,p in enumerate(pair)}
   def flip(g):
    assert all(pos[g[pair[0]-1]][0]==i and pos[g[pair[1]-1]][0]==i for i,pair in enumerate(frame))
    return sum(pos[g[pair[0]-1]][1]<<i for i,pair in enumerate(frame))
   k=basis(map(flip,rec['kernel_generators']));key=(t['id'],k)
   if key not in modules:modules[key]={'top_id':t['id'],'width':t['width'],'kernel_basis':k,'contexts':[]}
   modules[key]['contexts'].append([node,frame])
 result=[]
 for mid,(key,m) in enumerate(sorted(modules.items())):
  t=tops[m['top_id']];m.update(id=mid,axes=submodules(m['kernel_basis'],t['rows']));result.append(m)
 return tops,result

def chart(w,b,name):
 d=len(b);mat=[[x>>i&1 for x in b] for i in range(w)];piv=[x.bit_length()-1 for x in b]
 rows=['#['+','.join(map(str,r))+']' for r in mat]
 incl=f'(({lookup(rows,"i.val")} : Array (ZMod 2))[j.val]!)'
 coords=lookup(piv,'j.val') if piv else '0'
 return f'''def {name} : BinaryCoordinateSpace {w} {d} where
  inclusion := Matrix.mulVecLin (fun i j => {incl})
  coordinates := {{
    toFun v j := v ({coords})
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }}
  left_inverse := by decide +kernel

'''

def emit(t,m):
 mid=m['id'];sid=t['id'];w=m['width'];k=m['kernel_basis'];ds=len(k);axes=m['axes'];n=len(axes);ix={a:i for i,a in enumerate(axes)};top=t['rows'];S=f'BinaryTopSource{sid:03d}';label=f'{mid:03d}';order=len(top);ng=len(t['generators'])
 arrays=lambda data:['#['+','.join(map(str,a))+']' for a in data]
 inverse_rows=[tuple(p.index(i) for i in range(w)) for p in top]
 s=f'''import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry
import SymmetricSubgroupAsymptotics.BinaryFiniteCoordinateAction
import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorChecks
import SymmetricSubgroupAsymptotics.GeneratedTopNormals.Source{sid:03d}

/-! Complete invariant axes for one literal correlated flip module.
Reversible charts, actual generator stability and sparse orbit joins are
kernel checked. No normal-lift enumeration is a proof premise. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryKernelAxes{label}
abbrev Source := FiniteGroupRow {order}
local instance : Group Source := {S}.group

def generators (j : Fin {ng}) : Source :=
  ⟨{S}.certificate.next {S}.certificate.identity j⟩

theorem generators_full : Subgroup.closure (Set.range generators)=⊤ :=
  {S}.certificate.row_generators_full {S}.rows_injective {S}.prevRow {S}.prev_checked

def permutation : Source →* Equiv.Perm (Fin {w}) :=
  (Subgroup.closure (Set.range {S}.generators)).subtype.comp {S}.originalEquiv.toMonoidHom
def action : Representation (ZMod 2) Source (Fin {w} → ZMod 2) :=
  (binaryPermutationRepresentation {w}).comp permutation

/-- Numeric rows are checked once against the exact original encoding. -/
def rowPermutation (g : Source) : Equiv.Perm (Fin {w}) where
  toFun x := ({lookup(arrays(top),'g.index.val')} : Array (Fin {w}))[x.val]!
  invFun x := ({lookup(arrays(inverse_rows),'g.index.val')} : Array (Fin {w}))[x.val]!
  left_inv := by revert g; decide +kernel
  right_inv := by revert g; decide +kernel
private theorem row_checked : ∀ (g : Source) (x : Fin {w}),
    rowPermutation g x=finFunctionFinEquiv.symm ({S}.certificate.rows g.index) x := by decide +kernel

theorem rowPermutation_eq_original (g : Source) :
    rowPermutation g=({S}.originalEquiv g : Equiv.Perm (Fin {w})) := by
  apply Equiv.ext
  intro x
  change rowPermutation g x={S}.certificate.toCayley.elements g.index x
  rw [{S}.certificate.permutation_elements_apply]
  exact row_checked g x

theorem permutation_eq_row (g : Source) : permutation g=rowPermutation g :=
  (rowPermutation_eq_original g).symm
theorem rowPermutation_injective : Function.Injective rowPermutation := by
  intro g h he
  apply {S}.originalEquiv.injective
  apply Subtype.ext
  simpa only [rowPermutation_eq_original] using he
theorem rowPermutation_mul (g h : Source) :
    rowPermutation (g*h)=rowPermutation g*rowPermutation h := by
  simpa only [permutation_eq_row] using permutation.map_mul g h
theorem row_mul_eq_iff (g h k : Source) :
    g*h=k ↔ rowPermutation g*rowPermutation h=rowPermutation k := by
  constructor
  · intro he
    simpa only [rowPermutation_mul] using congrArg rowPermutation he
  · intro he
    apply rowPermutation_injective
    simpa only [rowPermutation_mul] using he
theorem row_commute_iff (g h : Source) :
    g*h=h*g ↔ rowPermutation g*rowPermutation h=rowPermutation h*rowPermutation g := by
  constructor
  · intro he
    simpa only [rowPermutation_mul] using congrArg rowPermutation he
  · intro he
    apply rowPermutation_injective
    simpa only [rowPermutation_mul] using he

theorem action_numeric (g : Source) :
    action g=binaryPermutationRepresentation {w} (rowPermutation g) := by
  rw [rowPermutation_eq_original]
  rfl
theorem action_inverse_numeric (g : Source) :
    action g⁻¹=binaryPermutationRepresentation {w} (rowPermutation g)⁻¹ := by
  change binaryPermutationRepresentation {w} (permutation g⁻¹)=_
  rw [map_inv,rowPermutation_eq_original]
  rfl

'''
 for i,a in enumerate(axes):
  s+=chart(w,a,f'chart{i}')
  s+=f'''private theorem positive{i} : ∀ i j,
    action (generators i) (chart{i}.inclusion (Pi.single j 1))∈chart{i}.space := by
  simp only [action_numeric]
  decide +kernel
private theorem negative{i} : ∀ i j,
    action (generators i)⁻¹ (chart{i}.inclusion (Pi.single j 1))∈chart{i}.space := by
  simp only [action_inverse_numeric]
  decide +kernel

def state{i} : Subrepresentation action :=
  chart{i}.subrepresentationOfGenerators action generators generators_full positive{i} negative{i}

'''
 s+=f'''def charts (i : Fin {n}) : Σ d, BinaryCoordinateSpace {w} d :=
  {lookup([f'⟨{len(a)},chart{i}⟩' for i,a in enumerate(axes)])}
def states (i : Fin {n}) : Subrepresentation action :=
  {lookup([f'state{i}' for i in range(n)])}

theorem states_space (i : Fin {n}) : (states i).toSubmodule=(charts i).2.space := by
  fin_cases i <;> rfl

abbrev kernelChart := chart{n-1}
abbrev kernel := state{n-1}

private def code (v : Fin {ds} → ZMod 2) : ℕ := ∑ i, (v i).val*2^i.val
'''
 child=[];olds=[];orbitids=[];orbitlists=[()];oi={():0}
 for a in axes:
  for code in range(1<<ds):
   v=vector(k,code);pool=list(a)+[act(p,v) for p in top];b=basis(pool);child.append(ix[b]);oo=[];gg=[]
   for x in b:
    mask=decompose(pool,x);oo.append(mask&((1<<len(a))-1));gl=tuple(i for i in range(order) if mask>>(len(a)+i)&1)
    if gl not in oi:oi[gl]=len(orbitlists);orbitlists.append(gl)
    gg.append(oi[gl])
   olds.append(oo);orbitids.append(gg)
 arrays=lambda data:['#['+','.join(map(str,a))+']' for a in data]
 index=f'i.val*{1<<ds}+code a'
 s+=f'''
private def child (i : Fin {n}) (a : Fin {ds} → ZMod 2) : Fin {n} :=
  {lookup(child,index)}
private def old (i : Fin {n}) (a : Fin {ds} → ZMod 2)
    (j : Fin (charts (child i a)).1) (b : Fin (charts i).1) : ZMod 2 :=
  if Nat.testBit (({lookup(arrays(olds),index)} : Array ℕ)[j.val]!) b.val then 1 else 0
private def orbitLists (i : Fin {len(orbitlists)}) : List Source :=
  {lookup(['['+','.join(f'⟨{x}⟩' for x in gl)+']' for gl in orbitlists])}
private def orbit (i : Fin {n}) (a : Fin {ds} → ZMod 2)
    (j : Fin (charts (child i a)).1) : List Source :=
  orbitLists (({lookup(arrays(orbitids),index)} : Array (Fin {len(orbitlists)}))[j.val]!)

private theorem old_mem : ∀ i a j,
    (charts i).2.inclusion (Pi.single j 1)∈(charts (child i a)).2.space := by decide +kernel
private theorem point_mem : ∀ i a,
    kernelChart.inclusion a∈(charts (child i a)).2.space := by decide +kernel
private theorem generated : ∀ i a j,
    (charts (child i a)).2.inclusion (Pi.single j 1)=
      (charts i).2.inclusion (old i a j)+
      ((orbit i a j).map (fun g => action g (kernelChart.inclusion a))).sum := by
  simp only [action_numeric]
  decide +kernel
private theorem le_kernel_basis : ∀ i j,
    (charts i).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel

private theorem child_eq (i : Fin {n}) (a : Fin {ds} → ZMod 2) :
    (states (child i a)).toSubmodule=(states i).toSubmodule⊔
      binaryOrbitSpan (k := ZMod 2) action (kernelChart.inclusion a) := by
  rw [states_space (child i a),states_space i]
  exact binaryCoordinate_orbit_join_eq (charts i).2 (charts (child i a)).2
    action (states (child i a)) (states_space (child i a)) (kernelChart.inclusion a)
    (old_mem i a) (point_mem i a) (old i a) (orbit i a) (generated i a)

def registry : BinaryInvariantKernelRegistry action kernel states where
  le_kernel i := by
    rw [states_space]
    exact (charts i).2.le_of_basis_mem kernelChart.space (le_kernel_basis i)
  bottom := 0
  bottom_eq := by
    change chart0.space=⊥
    apply le_antisymm
    · apply chart0.le_of_basis_mem
      intro j
      exact Fin.elim0 j
    · exact bot_le
  child i v := child i (kernelChart.coordinates v)
  child_eq i v := by
    have he : kernelChart.inclusion (kernelChart.coordinates v)=(v:Fin {w} → ZMod 2) :=
      (kernelChart.mem_iff v).mp v.property
    exact (child_eq i (kernelChart.coordinates v)).trans (by rw [he])

/-- Every actual invariant subspace of this retained kernel is listed. -/
theorem complete (W : Subrepresentation action) (hW : W.toSubmodule≤kernel.toSubmodule) :
    ∃ i, states i=W := registry.complete W hW

end SymmetricSubgroupAsymptotics.BinaryKernelAxes{label}
'''
 return OUT/f'Axes{label}.lean',s

def pilot_modules(t,m,whole):
 """Split only the selected pilot; retain the canonical emitter verbatim.

 Each axis has its own chart, join witness data, and finite join proofs.
 The final PilotNNN assembles the same complete invariant registry used by
 cuts and bindings. No declaration is discharged by importing a sibling
 with an assumed completeness statement.
 """
 mid=m['id'];tag=f'{mid:03d}';sid=t['id'];w=m['width'];k=m['kernel_basis']
 ds=len(k);axes=m['axes'];n=len(axes);top=t['rows'];order=len(top)
 ix={tuple(a):i for i,a in enumerate(axes)}
 namespace=f'SymmetricSubgroupAsymptotics.BinaryKernelAxes{tag}'
 prefix='SymmetricSubgroupAsymptotics.GeneratedKernelAxes.'
 outputs={}
 def module(name,body):outputs[OUT/f'{name}.lean']=body
 def header(imports,instance_name):
  return ''.join(f'import {prefix}{name}\n' for name in imports)+f'''
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace {namespace}
local instance {instance_name} : Group Source := BinaryTopSource{sid:03d}.group

'''
 close=f'end {namespace}\n'
 charts_start=whole.index('def chart0 :')
 states_start=whole.index('def charts (')
 code_start=whole.index('private def code ')
 base=whole[:charts_start].replace(
  f'.GeneratedTopNormals.Source{sid:03d}',f'.GeneratedTopNormals.Pilot{sid:03d}')
 base=base.replace('local instance : Group Source :=','local instance pilotBaseGroup : Group Source :=')
 module(f'PilotBase{tag}',base+close)
 chart_modules=[]
 for i in range(n):
  name=f'PilotChart{tag}_{i:03d}';chart_modules.append(name)
  start=whole.index(f'def chart{i} :')
  end=whole.index(f'def chart{i+1} :') if i+1<n else states_start
  module(name,header([f'PilotBase{tag}'],f'pilotChart{i:03d}Group')+whole[start:end]+close)
 module(f'PilotStates{tag}',header(chart_modules,'pilotStatesGroup')+whole[states_start:code_start]+close)
 join_modules=[]
 for ai,a in enumerate(axes):
  child=[];olds=[];orbitids=[];orbitlists=[()];orbit_index={():0}
  for bits in range(1<<ds):
   v=vector(k,bits);pool=list(a)+[act(p,v) for p in top]
   b=basis(pool);child.append(ix[b]);oo=[];gg=[]
   for x in b:
    mask=decompose(pool,x);oo.append(mask&((1<<len(a))-1))
    gl=tuple(i for i in range(order) if mask>>(len(a)+i)&1)
    if gl not in orbit_index:
     orbit_index[gl]=len(orbitlists);orbitlists.append(gl)
    gg.append(orbit_index[gl])
   olds.append(oo);orbitids.append(gg)
  arrays=lambda rows:['#['+','.join(map(str,row))+']' for row in rows]
  jointag=f'PilotJoin{ai:03d}';data_name=f'PilotJoinData{tag}_{ai:03d}'
  proof_name=f'PilotJoin{tag}_{ai:03d}';join_modules.append(proof_name)
  data=f'''namespace {jointag}
def code (v : Fin {ds} → ZMod 2) : ℕ := ∑ i, (v i).val*2^i.val
def child (a : Fin {ds} → ZMod 2) : Fin {n} :=
  {lookup(child,'code a')}
def old (a : Fin {ds} → ZMod 2)
    (j : Fin (charts (child a)).1) (b : Fin (charts {ai}).1) : ZMod 2 :=
  if Nat.testBit (({lookup(arrays(olds),'code a')} : Array ℕ)[j.val]!) b.val then 1 else 0
def orbitLists (i : Fin {len(orbitlists)}) : List Source :=
  {lookup(['['+','.join(f'⟨{x}⟩' for x in gl)+']' for gl in orbitlists])}
def orbit (a : Fin {ds} → ZMod 2)
    (j : Fin (charts (child a)).1) : List Source :=
  orbitLists (({lookup(arrays(orbitids),'code a')} : Array (Fin {len(orbitlists)}))[j.val]!)
end {jointag}

'''
  module(data_name,header([f'PilotStates{tag}'],f'pilotJoinData{ai:03d}Group')+data+close)
  proof=f'''namespace {jointag}
private theorem old_mem : ∀ a j,
    (charts {ai}).2.inclusion (Pi.single j 1)∈(charts (child a)).2.space := by decide +kernel
private theorem point_mem : ∀ a,
    kernelChart.inclusion a∈(charts (child a)).2.space := by decide +kernel
private theorem generated : ∀ a j,
    (charts (child a)).2.inclusion (Pi.single j 1)=
      (charts {ai}).2.inclusion (old a j)+
      ((orbit a j).map (fun g => action g (kernelChart.inclusion a))).sum := by
  simp only [action_numeric]
  decide +kernel
theorem le_kernel_basis : ∀ j,
    (charts {ai}).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel

theorem child_eq (a : Fin {ds} → ZMod 2) :
    (states (child a)).toSubmodule=(states {ai}).toSubmodule⊔
      binaryOrbitSpan (k := ZMod 2) action (kernelChart.inclusion a) := by
  rw [states_space (child a),states_space {ai}]
  exact binaryCoordinate_orbit_join_eq (charts {ai}).2 (charts (child a)).2
    action (states (child a)) (states_space (child a)) (kernelChart.inclusion a)
    (old_mem a) (point_mem a) (old a) (orbit a) (generated a)
end {jointag}

'''
  module(proof_name,header([data_name],f'pilotJoinProof{ai:03d}Group')+proof+close)
 assembly=f'''private def child (i : Fin {n}) (a : Fin {ds} → ZMod 2) : Fin {n} :=
  {lookup([f'PilotJoin{i:03d}.child a' for i in range(n)])}
private theorem le_kernel_basis : ∀ i j,
    (charts i).2.inclusion (Pi.single j 1)∈kernelChart.space := by
  intro i
  fin_cases i
'''
 for i in range(n):assembly+=f'  · exact PilotJoin{i:03d}.le_kernel_basis\n'
 assembly+=f'''
private theorem child_eq (i : Fin {n}) (a : Fin {ds} → ZMod 2) :
    (states (child i a)).toSubmodule=(states i).toSubmodule⊔
      binaryOrbitSpan (k := ZMod 2) action (kernelChart.inclusion a) := by
  fin_cases i
'''
 for i in range(n):assembly+=f'  · exact PilotJoin{i:03d}.child_eq a\n'
 assembly+='\n'+whole[whole.index('def registry :'):]
 module(f'Pilot{tag}',header(join_modules,'pilotRegistryGroup')+assembly)
 return outputs

def cut_choices(t,m):
 axes=m['axes'];ix={a:i for i,a in enumerate(axes)};kk=span(m['kernel_basis']);ss={a:span(a) for a in axes};pg=t['generators'];cuts=[];fixed=[]
 for a in axes:
  options=[]
  for c in axes:
   if not ss[a]<=ss[c] or not all(act(p,v)^v in ss[a] for p in pg for v in c):continue
   D=basis(v for v in kk if all(act(p,v)^v in ss[c] for p in pg));assert D in ix
   options.append((2*(len(c)-len(a))+4*(len(D)-len(c)),ix[c],ix[D]))
  _,ci,di=min(options);cuts.append(ci);fixed.append(di)
 m['cuts']=cuts;m['fixed']=fixed

def fixed_factors(t,m):
 """Sparse row-factor witnesses for defect(D)=R*generatorDefects(C) on K."""
 def projection(b,v):
  return vector(b,sum(((v>>(x.bit_length()-1))&1)<<j for j,x in enumerate(b)))
 factors=[];k=m['kernel_basis'];w=m['width']
 for ci,di in zip(m['cuts'],m['fixed']):
  c=m['axes'][ci];d=m['axes'][di]
  columns=[]
  for x in k:
   col=[]
   for p in t['generators']:
    delta=act(p,x)^x;defect=delta^projection(c,delta)
    col.extend((defect>>l)&1 for l in range(w))
   columns.append(col)
  constraints=[sum(col[j]<<i for i,col in enumerate(columns)) for j in range(len(t['generators'])*w)]
  rows=[]
  for l in range(w):
   target=sum(((x^projection(d,x))>>l&1)<<i for i,x in enumerate(k));mask=decompose(constraints,target)
   selected=[j for j in range(len(constraints)) if mask>>j&1]
   check=0
   for j in selected:check^=constraints[j]
   assert check==target
   rows.append([(j//w,j%w) for j in selected])
  factors.append(rows)
 return factors

def emit_cuts(t,m):
 mid=m['id'];w=m['width'];n=len(m['axes']);ng=len(t['generators'])
 factors=fixed_factors(t,m)
 entries=['['+','.join(f'({j},{l})' for j,l in row)+']' for rows in factors for row in rows]
 return f'''
namespace SymmetricSubgroupAsymptotics.BinaryKernelCuts{mid:03d}
open BinaryKernelAxes{mid:03d}
local instance : Group Source := BinaryTopSource{t['id']:03d}.group

def cutIndex (i : Fin {n}) : Fin {n} := {lookup(m['cuts'])}
def fixedIndex (i : Fin {n}) : Fin {n} := {lookup(m['fixed'])}

private theorem axis_le_cut_basis : ∀ i j,
    (charts i).2.inclusion (Pi.single j 1)∈(charts (cutIndex i)).2.space := by decide +kernel
private theorem cut_le_kernel_basis : ∀ i j,
    (charts (cutIndex i)).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel
private theorem central_basis : ∀ i j l,
    action (generators j) ((charts (cutIndex i)).2.inclusion (Pi.single l 1))-
      (charts (cutIndex i)).2.inclusion (Pi.single l 1)∈(charts i).2.space := by
  simp only [action_numeric]
  decide +kernel
private def factorEntries (i : Fin {n}) (l : Fin {w}) : List (Fin {ng} × Fin {w}) :=
  {lookup(entries,f'i.val*{w}+l.val')}
private def factor (i : Fin {n}) :
    (Fin {ng} → Fin {w} → ZMod 2) →ₗ[ZMod 2] (Fin {w} → ZMod 2) :=
  LinearMap.pi (fun l => ((factorEntries i l).map
    (fun p => (LinearMap.proj p.2 : (Fin {w} → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp
      (LinearMap.proj p.1 : (Fin {ng} → Fin {w} → ZMod 2) →ₗ[ZMod 2]
        (Fin {w} → ZMod 2)))).sum)
private theorem fixed_le_kernel_basis : ∀ i j,
    (charts (fixedIndex i)).2.inclusion (Pi.single j 1)∈kernelChart.space := by decide +kernel
private theorem fixed_basis : ∀ i j l,
    action (generators l) ((charts (fixedIndex i)).2.inclusion (Pi.single j 1))-
      (charts (fixedIndex i)).2.inclusion (Pi.single j 1)∈
        (charts (cutIndex i)).2.space := by
  simp only [action_numeric]
  decide +kernel
private theorem factor_basis : ∀ i j,
    (charts (fixedIndex i)).2.defect (kernelChart.inclusion (Pi.single j 1))=
      factor i (binaryCoordinate_generatorDefects action generators (charts (cutIndex i)).2
        (kernelChart.inclusion (Pi.single j 1))) := by
  simp only [binaryCoordinate_generatorDefects_apply,action_numeric]
  decide +kernel
private theorem full_fixed_predicate (i : Fin {n}) : ∀ v : Fin {w} → ZMod 2,
    v∈(charts (fixedIndex i)).2.space ↔ v∈kernelChart.space ∧
      ∀ j, action (generators j) v-v∈(charts (cutIndex i)).2.space :=
  binaryCoordinate_fixed_of_factor kernelChart (charts (cutIndex i)).2
    (charts (fixedIndex i)).2 action generators (factor i)
    (fixed_le_kernel_basis i) (fixed_basis i) (factor_basis i)

/-- The complete fixed preimage and central cut are certified actual spaces. -/
theorem certificate (i : Fin {n}) : BinaryCoordinateCutData action kernel
    (states i) (states (cutIndex i)) (states (fixedIndex i)) :=
  binaryCoordinate_cut_of_checks kernelChart (charts i).2 (charts (cutIndex i)).2
    (charts (fixedIndex i)).2 action kernel (states i) (states (cutIndex i))
    (states (fixedIndex i)) rfl (states_space i) (states_space (cutIndex i))
    (states_space (fixedIndex i)) generators generators_full (axis_le_cut_basis i)
    (cut_le_kernel_basis i) (central_basis i) (full_fixed_predicate i)

def cost (i : Fin {n}) : ℕ :=
  2*((charts (cutIndex i)).1-(charts i).1)+
    4*((charts (fixedIndex i)).1-(charts (cutIndex i)).1)

theorem cost_eq_actual_finranks (i : Fin {n}) : cost i=
    2*(Module.finrank (ZMod 2) (states (cutIndex i)).toSubmodule-
      Module.finrank (ZMod 2) (states i).toSubmodule)+
    4*(Module.finrank (ZMod 2) (states (fixedIndex i)).toSubmodule-
      Module.finrank (ZMod 2) (states (cutIndex i)).toSubmodule) := by
  rw [states_space (cutIndex i),states_space i,states_space (fixedIndex i),
    (charts (cutIndex i)).2.finrank,(charts i).2.finrank,(charts (fixedIndex i)).2.finrank]
  rfl
end SymmetricSubgroupAsymptotics.BinaryKernelCuts{mid:03d}
'''

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--module',type=int,action='append')
 ap.add_argument('--batch',type=int,action='append')
 ap.add_argument('--pilot-module',type=int,help='Emit a modular single-axis-registry pilot and CutsPilotNNN from the existing inventory; leave canonical files and index unchanged.')
 ap.add_argument('--from-index',action='store_true',help='Reuse the existing finite inventory; emit only the selected batches without recomputing submodules.')
 ap.add_argument('--check',action='store_true');args=ap.parse_args()
 if args.pilot_module is not None:
  if args.module is not None or args.batch is not None:ap.error('--pilot-module cannot be combined with --module or --batch')
  args.from_index=True
 if args.from_index:
  tops=json.loads((ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedTopNormals/index.json').read_text())
  modules=json.loads((OUT/'index.json').read_text())
  grouped={}
  for m in modules:
   m['kernel_basis']=tuple(m['kernel_basis']);m['axes']=[tuple(a) for a in m['axes']]
   grouped.setdefault(int(m['batch'][5:]),[]).append(m)
  batches=sorted(grouped.items())
  if args.pilot_module is not None:
   selected=[m for m in modules if m['id']==args.pilot_module]
   if not selected:ap.error('Unknown pilot module')
   batches=[(args.pilot_module,selected)]
 else:
  tops,modules=inventory()
  for m in modules:cut_choices(tops[m['top_id']],m)
  batches=[];current=[];weight=0;source_batch=None
  for m in modules:
   sb=tops[m['top_id']]['batch'];work=len(m['axes'])*(1<<len(m['kernel_basis']))
   if current and (sb!=source_batch or weight+work>12000):batches.append(current);current=[];weight=0
   current.append(m);weight+=work;source_batch=sb
  if current:batches.append(current)
  batches=list(enumerate(batches))
 OUT.mkdir(exist_ok=True)
 outputs={}
 for bi,batch in batches:
  name=f'Pilot{bi:03d}' if args.pilot_module is not None else f'Batch{bi:03d}'
  if args.pilot_module is None:
   for m in batch:m['batch']=name
  if args.batch is not None and bi not in args.batch:continue
  if args.module is not None and not any(m['id'] in args.module for m in batch):continue
  parts=[];cutparts=[];imports=set()
  for m in batch:
   path,s=emit(tops[m['top_id']],m)
   if args.pilot_module is not None:outputs.update(pilot_modules(tops[m['top_id']],m,s))
   for line in s.splitlines():
    if line.startswith('import '):
     if '.GeneratedTopNormals.Source' in line:
      top_module=f"Pilot{m['top_id']:03d}" if args.pilot_module is not None else f"Batch{tops[m['top_id']]['batch']:03d}"
      line=f"import SymmetricSubgroupAsymptotics.GeneratedTopNormals.{top_module}"
     imports.add(line)
   parts.append('\n'.join(line for line in s.splitlines() if not line.startswith('import ')))
   cutparts.append(emit_cuts(tops[m['top_id']],m))
   if args.pilot_module is None:
    outputs[path]=f'import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.{name}\n'
    outputs[OUT/f"Cuts{m['id']:03d}.lean"]=f'import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.Cuts{name}\n'
  if args.pilot_module is None:
   outputs[OUT/f'{name}.lean']='\n'.join(sorted(imports))+'\n\n'+'\n'.join(parts)+'\n'
  outputs[OUT/f'Cuts{name}.lean']=(
   f'import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.{name}\n'
   'import SymmetricSubgroupAsymptotics.BinaryCoordinateCuts\n'
   'import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor\n\n'
   'set_option autoImplicit false\nset_option maxHeartbeats 0\n'
   'set_option maxRecDepth 100000\nset_option linter.unusedVariables false\n'
   'noncomputable section\n\n'+'\n'.join(cutparts)+'\n')
 for path,s in outputs.items():
  b=s.encode()
  if args.check:
   if not path.exists() or path.read_bytes()!=b:raise SystemExit(f'Stale generated file {path}')
  elif not path.exists() or path.read_bytes()!=b:path.write_bytes(b)
  print(path.relative_to(ROOT),flush=True)
 if args.pilot_module is not None:return
 index=json.dumps(modules,indent=2)+'\n'
 if args.check:
  if (OUT/'index.json').read_text()!=index:raise SystemExit('Stale kernel axis index')
 else:(OUT/'index.json').write_text(index)
if __name__=='__main__':main()
