#!/usr/bin/env python3
"""Bind each original pair action to its shared literal top and flip module.

Original generator images, a quotient-sized Schreier system and short
original words for the kernel basis are checked. Two-way generator words
identify the original top. No source order, normal-lift enumeration or
replacement by independent flips is a premise.
"""
import argparse,gzip,json
from pathlib import Path
from export_lean_menu_cayley import ROOT,table,packed,lookup,array,compose
from export_lean_normal_registry import inv
from export_lean_kernel_axes import decompose,span,act,vector
from export_lean_kernel_gaps import central_data,exceptional_axes
OUT=ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedPairBindings'

def permutation(name,p):
 w=len(p)
 return f'''private def {name} : Equiv.Perm (Fin {w}) where
  toFun x := ({array(p)} : Array (Fin {w}))[x.val]!
  invFun x := ({array(inv(p))} : Array (Fin {w}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''

def word(st,r):
 result=[]
 while r!=st['identity']:result.append(st['letter'][r]);r=st['parent'][r]
 return result[::-1]

def schreier_data(gs,tops,frame,t,kernel_basis):
 """Quotient-sized section plus at most eight literal kernel basis words.

 No original source elements or source Cayley table are enumerated. The
 section has one entry per shared top row; Gaussian elimination combines
 its Schreier flips into the retained original kernel basis. All resulting
 point equations are checked again by the generated Lean declarations.
 """
 w=len(gs[0]);h=w//2;points=[x-1 for p in frame for x in p]
 pair={x:i//2 for i,x in enumerate(points)};bit={x:i%2 for i,x in enumerate(points)}
 qt=table(tops,h)
 assert qt['codes']==[packed(p) for p in t['rows']]
 assert len(qt['codes'])==t['order']<=128
 section_words=[word(qt,q) for q in range(t['order'])]
 def evaluate(ws):
  p=tuple(range(w))
  for j in ws:p=compose(p,gs[j])
  return p
 orders=[]
 for g in gs:
  p=g;order=1
  while p!=tuple(range(w)):
   p=compose(p,g);order+=1
  orders.append(order)
 def inverse_word(ws):
  return [j for j in reversed(ws) for _ in range(orders[j]-1)]
 def shorten(ws):
  out=[]
  for j in ws:
   out.append(j)
   if len(out)>=orders[j] and all(x==j for x in out[-orders[j]:]):
    del out[-orders[j]:]
  return out
 lifts=list(map(evaluate,section_words));ti={tuple(p):i for i,p in enumerate(t['rows'])}
 images=[ti[p] for p in tops];masks=[];words=[]
 for q,p in enumerate(t['rows']):
  for j,g in enumerate(gs):
   qp=ti[compose(p,tops[j])];z=compose(compose(lifts[q],g),inv(lifts[qp]))
   assert all(pair[z[x]]==pair[x] for x in range(w))
   masks.append(sum(bit[z[frame[i][0]-1]]<<i for i in range(h)))
   ws=shorten(section_words[q]+[j]+inverse_word(section_words[qp]))
   assert evaluate(ws)==z
   words.append(ws)
 pool=sorted(range(len(masks)),key=lambda j:(len(words[j]),words[j]))
 basis_words=[]
 for v in kernel_basis:
  coefficients=decompose([masks[j] for j in pool],v)
  ws=shorten([letter for i,j in enumerate(pool) if coefficients>>i&1 for letter in words[j]])
  target=tuple(points[2*pair[x]+(bit[x]^((v>>pair[x])&1))] for x in range(w))
  assert evaluate(ws)==target
  basis_words.append(ws)
 return section_words,images,masks,basis_words

def central_obstructions(gs,tops,frame,m,t,section_words):
 """Sparse inconsistent affine-equation witnesses; never enumerate K or U."""
 result=[];w=m['width'];d=len(m['kernel_basis']);degree=2*w
 points=[x-1 for p in frame for x in p]
 pair={x:i//2 for i,x in enumerate(points)};bit={x:i%2 for i,x in enumerate(points)}
 def evaluate(ws):
  p=tuple(range(degree))
  for j in ws:p=compose(p,gs[j])
  return p
 def projection(a,v):return vector(a,sum(((v>>(x.bit_length()-1))&1)<<j for j,x in enumerate(a)))
 identity=next(q for q,p in enumerate(t['rows']) if tuple(p)==tuple(range(w)))
 for ai in exceptional_axes(t,m):
  a=m['axes'][ai];aa=span(a);candidates=[];obstructions=[]
  columns=[]
  for v in m['kernel_basis']:
   col=[]
   for p in tops:
    dv=act(p,v)^v;dv^=projection(a,dv)
    col.extend((dv>>l)&1 for l in range(w))
   columns.append(col)
  constraints=[sum(col[j]<<i for i,col in enumerate(columns)) for j in range(len(gs)*w)]
  for q,p in enumerate(t['rows']):
   if q==identity or not all(act(p,v)^v in aa for v in m['kernel_basis']):continue
   if not all(compose(p,g)==compose(g,p) for g in tops):continue
   candidates.append(q)
   s=evaluate(section_words[q]);comm=[];constant=[]
   for g in gs:
    c=compose(compose(compose(inv(s),g),s),inv(g))
    assert all(pair[c[x]]==pair[x] for x in range(degree))
    v=sum(bit[c[frame[l][0]-1]]<<l for l in range(w));comm.append(v)
    v^=projection(a,v);constant.extend((v>>l)&1 for l in range(w))
   try:mask=decompose([r|(b<<d) for r,b in zip(constraints,constant)],1<<d)
   except AssertionError:continue
   selected=[j for j in range(len(constraints)) if mask>>j&1]
   zero=0;one=0
   for j in selected:zero^=constraints[j];one^=constant[j]
   assert zero==0 and one==1
   obstructions.append({'top':q,'commutators':comm,'entries':[(j//w,j%w) for j in selected]})
  result.append({'axis':ai,'candidates':candidates,'obstructions':obstructions,
                 'complete':bool(candidates) and len(candidates)==len(obstructions)})
 return result

def emit_obstructions(node,m,t,data):
 """Original section equations install the sparse affine exclusions."""
 label=node['id'][1:].replace('_','T');A=f'BinaryKernelAxes{m["id"]:03d}'
 w=m['width'];ng=len(node['generators']);out=''
 for record in data:
  if not record['obstructions']:continue
  ai=record['axis'];normal=f'centralNormal{ai}';axis=f'centralAxis{ai}'
  out+=f'''
private def {axis} : Subrepresentation physicalFrame.coordinateTopAction :=
  physicalFrame.sharedSubrepresentation {A}.action topEquiv action_eq ({A}.states {ai})
private abbrev {normal} := physicalFrame.coordinateSubgroup {axis}.toSubmodule
'''
  for obstruction in record['obstructions']:
   q=obstruction['top'];tag=f'axis{ai}Top{q}'
   terms='['+','.join(f'({j},{l})' for j,l in obstruction['entries'])+']'
   out+=f'''
private theorem {tag}_top : ∀ j,
    (⟨{q}⟩:SourceTop)*images j=images j*⟨{q}⟩ := by
  simp only [{A}.row_commute_iff]
  decide +kernel
private def {tag}_commutator (j : Fin {ng}) : physicalFrame.top.ker :=
  ⟨(sectionMap ⟨{q}⟩)⁻¹*(generators j*sectionMap ⟨{q}⟩*(generators j)⁻¹),by
    rw [← sourceMap_kernel]
    change sourceMap ((sectionMap ⟨{q}⟩)⁻¹*(generators j*sectionMap ⟨{q}⟩*(generators j)⁻¹))=1
    simp only [map_mul,map_inv,section_right,sourceMap_generator]
    rw [← {tag}_top j]
    simp only [mul_assoc,mul_inv_cancel,mul_one,inv_mul_cancel]⟩
private def {tag}_factor : (Fin {ng} → Fin {w} → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (({terms} : List (Fin {ng} × Fin {w})).map
    (fun p => (LinearMap.proj p.2).comp (LinearMap.proj p.1))).sum
private theorem {tag}_zero : ∀ i,
    {tag}_factor (binaryCoordinate_generatorDefects {A}.action images ({A}.charts {ai}).2
      ({A}.kernelChart.inclusion (Pi.single i 1)))=0 := by
  simp only [binaryCoordinate_generatorDefects_apply,{A}.action_numeric]
  decide +kernel
private theorem {tag}_nonzero :
    {tag}_factor (fun j => ({A}.charts {ai}).2.defect
      (physicalFrame.bits ({tag}_commutator j)))≠0 := by decide +kernel

private theorem {tag}_excludes (u : Original) (hq : sourceMap u=⟨{q}⟩)
    (hu : QuotientGroup.mk' {normal} u∈Subgroup.center (Original ⧸ {normal})) : False := by
  apply physicalFrame.central_quotient_obstruction {axis} ({A}.charts {ai}).2
    ({A}.states_space {ai}) {A}.kernelChart kernel_space generators (sectionMap ⟨{q}⟩)
    {tag}_commutator (fun _ => rfl) {tag}_factor ?_ {tag}_nonzero u ?_ hu
  · intro i
    change {tag}_factor (fun j => ({A}.charts {ai}).2.defect
      (physicalFrame.coordinateTopAction (physicalFrame.top.rangeRestrict (generators j))
        ({A}.kernelChart.inclusion (Pi.single i 1))-
          {A}.kernelChart.inclusion (Pi.single i 1)))=0
    simp_rw [← topEquiv_sourceMap,sourceMap_generator,← action_eq]
    exact {tag}_zero i
  · have he : sourceMap u=sourceMap (sectionMap ⟨{q}⟩) := hq.trans (section_right _).symm
    have h := congrArg topEquiv he
    simp only [topEquiv_sourceMap] at h
    exact congrArg Subtype.val h
'''
  if record['complete']:
   criterion=' ∨ '.join(['g=1']+[f'g=⟨{q}⟩' for q in record['candidates']])
   alternatives='|'.join(['hone']+[f'hq{q}' for q in record['candidates']])
   branches='\n'.join(f'  · exact (axis{ai}Top{q}_excludes u hq{q} hu).elim' for q in record['candidates'])
   out+=f'''
private theorem centralCandidates{ai} : ∀ g : SourceTop,
    (∀ j,g*images j=images j*g) →
    (∀ j,{A}.action g ({A}.kernelChart.inclusion (Pi.single j 1))-
      {A}.kernelChart.inclusion (Pi.single j 1)∈({A}.charts {ai}).2.space) → {criterion} := by
  simp only [{A}.row_commute_iff,{A}.action_numeric]
  decide +kernel

/-- Original section commutators exclude all nontrivial possible central
top components for this literal action and correlated normal. -/
theorem centralKernel{ai} (u : Original)
    (hu : QuotientGroup.mk' {normal} u∈Subgroup.center (Original ⧸ {normal})) :
    u∈physicalFrame.top.ker := by
  have ht : ∀ j,sourceMap u*images j=images j*sourceMap u := by
    intro j
    have hc := ((binaryPair_quotient_center_iff {normal} (fun x : Original => x)
      (by simp) u).mp hu) (generators j)
    have hk := physicalFrame.coordinateSubgroup_le_kernel {axis}.toSubmodule hc
    rw [← sourceMap_kernel] at hk
    change sourceMap (u⁻¹*(generators j*u*(generators j)⁻¹))=1 at hk
    simp only [map_mul,map_inv,sourceMap_generator] at hk
    rw [inv_mul_eq_one,eq_mul_inv_iff_mul_eq] at hk
    exact hk.symm
  have hb : ∀ j,{A}.action (sourceMap u) ({A}.kernelChart.inclusion (Pi.single j 1))-
      {A}.kernelChart.inclusion (Pi.single j 1)∈({A}.charts {ai}).2.space := by
    intro j
    have hv : {A}.kernelChart.inclusion (Pi.single j 1)∈physicalFrame.kernelSpace :=
      kernel_space.symm ▸ (show {A}.kernelChart.inclusion (Pi.single j 1)∈{A}.kernelChart.space from ⟨_,rfl⟩)
    obtain ⟨k,hk⟩ := hv
    change physicalFrame.bits k.toMul={A}.kernelChart.inclusion (Pi.single j 1) at hk
    rw [action_eq,topEquiv_sourceMap,← hk]
    rw [← {A}.states_space {ai}]
    exact physicalFrame.central_quotient_displacement {axis} u hu k.toMul
  rcases centralCandidates{ai} (sourceMap u) ht hb with {alternatives}
  · rw [← sourceMap_kernel]
    exact hone
{branches}
'''
 return out

def emit(node,frame,m,t,binding,axis_module=None):
 name=node['id'];label=name[1:].replace('_','T');G=f'BinaryActionData16.node{name.split("_")[1]}Generators'
 T=f'BinaryTopSource{t["id"]:03d}';A=f'BinaryKernelAxes{m["id"]:03d}'
 w=node['degree'];assert w==16;h=w//2;gs=[tuple(x-1 for x in g) for g in node['generators']]
 d=len(m['kernel_basis']);ng=len(gs)
 points=[x-1 for p in frame for x in p];pair={x:i//2 for i,x in enumerate(points)};bit={x:i%2 for i,x in enumerate(points)}
 tops=[tuple(pair[g[frame[i][0]-1]] for i in range(h)) for g in gs]
 section_words,images,masks,basis_words=schreier_data(gs,tops,frame,t,m['kernel_basis'])
 top_index={tuple(p):i for i,p in enumerate(t['rows'])}
 next_top=[top_index[compose(p,g)] for p in t['rows'] for g in tops]
 obstructions=central_obstructions(gs,tops,frame,m,t,section_words)
 s=f'''import SymmetricSubgroupAsymptotics.BinaryPairSchreierBinding
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.BinaryGeneratorWords
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.{axis_module or m['batch']}
import SymmetricSubgroupAsymptotics.GeneratedAction16.Data
{'import SymmetricSubgroupAsymptotics.BinaryPairCentralObstruction' if any(x['obstructions'] for x in obstructions) else ''}

/-! Exact original action, original generator top and correlated flip
kernel for {label}. All point and basis witnesses are checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding{label}
abbrev Original := Subgroup.closure (Set.range {G})
abbrev SourceTop := FiniteGroupRow {t['order']}
local instance : Group SourceTop := {T}.group

def generators (j : Fin {ng}) : Original := ⟨{G} j,Subgroup.subset_closure ⟨j,rfl⟩⟩
theorem generators_full : Subgroup.closure (Set.range generators)=⊤ :=
  binaryNormal_full_generators_of_equiv {G} generators (MulEquiv.refl _) (fun _ => rfl)

private def originalWord (ws : List (Fin {ng})) : Original :=
  ⟨(ws.map {G}).prod,Subgroup.list_prod_mem _ (by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure ⟨j,rfl⟩)⟩

def frame : Fin {h} × ZMod 2 ≃ Fin {w} where
  toFun p := ({array(points)} : Array (Fin {w}))[2*p.1.val+p.2.val]!
  invFun x := (({array([pair[x] for x in range(w)])} : Array (Fin {h}))[x.val]!,
    ({array([bit[x] for x in range(w)])} : Array (ZMod 2))[x.val]!)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''
 for j,p in enumerate(tops):s+=permutation(f'top{j}',p)
 s+=f'''def tops (j : Fin {ng}) : Equiv.Perm (Fin {h}) := {lookup([f'top{i}' for i in range(ng)],'j.val')}
private theorem preserves : ∀ j, BinaryPairFrame.Preserves frame ({G} j) (tops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def physicalFrame : BinaryPairFrame Original (Fin {h}) :=
  BinaryPairFrame.ofGenerators frame {G} tops preserves

private def originalToShared : BinaryNormalGeneratorWords tops {T}.generators where
  words j := {lookup([str(x).replace(' ','') for x in binding['original_to_shared']],'j.val')}
  equations := by decide +kernel
private def sharedToOriginal : BinaryNormalGeneratorWords {T}.generators tops where
  words j := {lookup([str(x).replace(' ','') for x in binding['shared_to_original']],'j.val')}
  equations := by decide +kernel

theorem top_range : physicalFrame.top.range=Subgroup.closure (Set.range {T}.generators) := by
  change (BinaryPairFrame.ofGenerators frame {G} tops preserves).top.range=_
  rw [BinaryPairFrame.ofGenerators_top_range]
  exact le_antisymm originalToShared.closure_le sharedToOriginal.closure_le

def topEquiv : SourceTop ≃* physicalFrame.top.range :=
  {T}.originalEquiv.trans (MulEquiv.subgroupCongr top_range.symm)

theorem action_eq : ∀ g v, {A}.action g v=physicalFrame.coordinateTopAction (topEquiv g) v := by
  intro g v
  rfl

def sourceMap : Original →* SourceTop := topEquiv.symm.toMonoidHom.comp physicalFrame.top.rangeRestrict
theorem topEquiv_sourceMap (u : Original) : topEquiv (sourceMap u)=physicalFrame.top.rangeRestrict u :=
  topEquiv.apply_symm_apply _
private def images (j : Fin {ng}) : SourceTop := ⟨{lookup(images,'j.val')}⟩
private theorem images_checked : ∀ j, tops j=({T}.originalEquiv (images j) : Equiv.Perm (Fin {h})) := by
  simp only [← {A}.rowPermutation_eq_original]
  decide +kernel
theorem sourceMap_generator (j : Fin {ng}) : sourceMap (generators j)=images j := by
  apply topEquiv.injective
  change topEquiv (topEquiv.symm (physicalFrame.top.rangeRestrict (generators j)))=_
  rw [topEquiv.apply_symm_apply]
  apply Subtype.ext
  change (BinaryPairFrame.ofGenerators frame {G} tops preserves).top
    ⟨{G} j,Subgroup.subset_closure ⟨j,rfl⟩⟩=_
  rw [BinaryPairFrame.ofGenerators_top_generator]
  exact images_checked j

theorem sourceMap_kernel : sourceMap.ker=physicalFrame.top.ker := by
  ext u
  change topEquiv.symm (physicalFrame.top.rangeRestrict u)=1 ↔ physicalFrame.top u=1
  constructor
  · intro hu
    have h := congrArg topEquiv hu
    simp only [topEquiv.apply_symm_apply,map_one] at h
    exact congrArg Subtype.val h
  · intro hu
    have h : physicalFrame.top.rangeRestrict u=1 := Subtype.ext hu
    rw [h,map_one]

private def sectionWords (q : SourceTop) : List (Fin {ng}) := {lookup([str(x).replace(' ','') for x in section_words],'q.index.val')}
def sectionMap (q : SourceTop) : Original := originalWord (sectionWords q)
private theorem section_checked : ∀ q, BinaryPairFrame.Preserves frame
    (sectionMap q : Equiv.Perm (Fin {w})) ({T}.originalEquiv q : Equiv.Perm (Fin {h})) := by
  unfold BinaryPairFrame.Preserves
  simp only [← {A}.rowPermutation_eq_original]
  decide +kernel
theorem section_right (q : SourceTop) : sourceMap (sectionMap q)=q := by
  apply topEquiv.injective
  change topEquiv (topEquiv.symm (physicalFrame.top.rangeRestrict (sectionMap q)))=_
  rw [topEquiv.apply_symm_apply]
  apply Subtype.ext
  exact BinaryPairFrame.preserves_unique frame (physicalFrame.intertwine (sectionMap q)) (section_checked q)
theorem section_identity : sectionMap 1=1 := by decide +kernel

private def nextTop (q : SourceTop) (j : Fin {ng}) : SourceTop :=
  ⟨{lookup(next_top,f'q.index.val*{ng}+j.val')}⟩
private theorem nextTop_checked : ∀ q j,q*images j=nextTop q j := by
  simp only [{A}.row_mul_eq_iff]
  decide +kernel
private def schreierElement (q : SourceTop) (j : Fin {ng}) : Original :=
  sectionMap q*generators j*(sectionMap (nextTop q j))⁻¹
private def schreierBits (q : SourceTop) (j : Fin {ng}) (i : Fin {h}) : ZMod 2 :=
  if Nat.testBit ({lookup(masks,f'q.index.val*{ng}+j.val')} : ℕ) i.val then 1 else 0
private theorem schreier_mem : ∀ q j, schreierBits q j∈{A}.kernelChart.space := by decide +kernel
private theorem schreier_action : ∀ q j (p : Fin {h} × ZMod 2),
    frame.symm ((schreierElement q j : Equiv.Perm (Fin {w})) (frame p))=
      (p.1,p.2+schreierBits q j p.1) := by decide +kernel

private def basisWords (i : Fin {d}) : List (Fin {ng}) := {lookup([str(x).replace(' ','') for x in basis_words]) if basis_words else 'Fin.elim0 i'}
private theorem basis_action : ∀ i : Fin {d}, ∀ p : Fin {h} × ZMod 2,
    frame.symm ((originalWord (basisWords i) : Equiv.Perm (Fin {w})) (frame p))=
      (p.1,p.2+{A}.kernelChart.inclusion (Pi.single i 1) p.1) := by decide +kernel

theorem kernel_space : physicalFrame.kernelSpace={A}.kernelChart.space := by
  apply physicalFrame.kernelSpace_eq_of_schreier {A}.kernelChart generators generators_full
    sourceMap sourceMap_kernel sectionMap section_right section_identity
  · intro q j
    change sectionMap q*generators j*(sectionMap (q*sourceMap (generators j)))⁻¹∈_
    rw [sourceMap_generator,nextTop_checked]
    exact physicalFrame.mem_coordinateSubgroup_of_action {A}.kernelChart.space
      (schreierElement q j) (schreierBits q j) (schreier_mem q j) (schreier_action q j)
  · intro i
    exact physicalFrame.vector_mem_kernelSpace_of_action (originalWord (basisWords i))
      ({A}.kernelChart.inclusion (Pi.single i 1)) (basis_action i)

{emit_obstructions(node,m,t,obstructions)}
end SymmetricSubgroupAsymptotics.BinaryPairBinding{label}
'''
 return s

def pilot_modules(node,m,t,whole):
 """Isolate exact original-action binding checks in deterministic small files.

 The numeric section and Schreier checks cover every quotient row, in
 blocks of at most 32. Their assembly only applies the checked blocks;
 the final kernel-space proof is the same original Schreier theorem.
 """
 label=node['id'][1:].replace('_','T');order=t['order'];ng=len(node['generators'])
 w=node['degree'];h=w//2;A=f'BinaryKernelAxes{m["id"]:03d}';T=f'BinaryTopSource{t["id"]:03d}'
 namespace=f'SymmetricSubgroupAsymptotics.BinaryPairBinding{label}'
 root=f'PilotBinding{label}';prefix='SymmetricSubgroupAsymptotics.GeneratedPairBindings.'
 outputs={};close=f'end {namespace}\n'
 def public(body):return body.replace('private def ','def ').replace('private theorem ','theorem ')
 def header(imports,instance_name):
  return ''.join(f'import {prefix}{name}\n' for name in imports)+f'''
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace {namespace}
local instance {instance_name} : Group SourceTop := {T}.group

'''
 def module(name,body):outputs[OUT/f'{name}.lean']=body
 def source_between(first,last):return whole[whole.index(first):whole.index(last)]
 def piece(name,imports,instance_name,body):module(root+name,header(imports,instance_name)+public(body)+close)
 base=whole[:whole.index('private def originalToShared')]
 base=public(base).replace('local instance : Group SourceTop :=','local instance pilotBaseGroup : Group SourceTop :=')
 module(root+'Base',base+close)
 piece('SourceMap',[root+'Base'],'pilotSourceMapGroup',source_between('private def originalToShared','private def sectionWords'))
 blocks=[(offset,min(32,order-offset)) for offset in range(0,order,32)]
 section_data=source_between('private def sectionWords','private theorem section_checked')
 piece('SectionData',[root+'SourceMap'],'pilotSectionDataGroup',section_data)
 def row_assembly(theorem,statement):
  body=f'theorem {theorem} : {statement} := by\n  intro q\n'
  for bi,(offset,count) in enumerate(blocks):
   indent='  '+'  '*bi
   lower='(Nat.zero_le _)' if bi==0 else f'(Nat.le_of_not_gt h{bi-1})'
   if bi+1==len(blocks):
    body+=indent+f'exact {theorem}{bi:03d} q {lower} q.index.isLt\n'
   else:
    body+=indent+f'by_cases h{bi} : q.index.val<{offset+count}\n'
    body+=indent+f'· exact {theorem}{bi:03d} q {lower} h{bi}\n'
    body+=indent+'·\n'
  return body+'\n'
 section_checks=[];schreier_checks=[]
 for bi,(offset,count) in enumerate(blocks):
  name=root+f'SectionCheck{bi:03d}';section_checks.append(name)
  body=f'''theorem section_checked{bi:03d} : ∀ q : SourceTop,
    {offset}≤q.index.val → q.index.val<{offset+count} → BinaryPairFrame.Preserves frame
    (sectionMap q : Equiv.Perm (Fin {w}))
    ({T}.originalEquiv q : Equiv.Perm (Fin {h})) := by
  unfold BinaryPairFrame.Preserves
  simp only [← {A}.rowPermutation_eq_original]
  decide +kernel
'''
  module(name,header([root+'SectionData'],f'pilotSectionCheck{bi:03d}Group')+body+close)
 section_assembly=row_assembly('section_checked',f'''∀ q, BinaryPairFrame.Preserves frame
    (sectionMap q : Equiv.Perm (Fin {w})) ({T}.originalEquiv q : Equiv.Perm (Fin {h}))''')
 section_assembly+='\n'+source_between('theorem section_right','private def nextTop')
 piece('Sections',section_checks,'pilotSectionsGroup',section_assembly)
 schreier_data=source_between('private def nextTop','private theorem nextTop_checked')
 schreier_data+=source_between('private def schreierElement','private theorem schreier_mem')
 piece('SchreierData',[root+'Sections'],'pilotSchreierDataGroup',schreier_data)
 for bi,(offset,count) in enumerate(blocks):
  name=root+f'SchreierCheck{bi:03d}';schreier_checks.append(name)
  body=f'''theorem nextTop_checked{bi:03d} : ∀ q : SourceTop,
    {offset}≤q.index.val → q.index.val<{offset+count} → ∀ j,
    q*images j=nextTop q j := by
  simp only [{A}.row_mul_eq_iff]
  decide +kernel
theorem schreier_mem{bi:03d} : ∀ q : SourceTop,
    {offset}≤q.index.val → q.index.val<{offset+count} → ∀ j,
    schreierBits q j∈{A}.kernelChart.space := by decide +kernel
theorem schreier_action{bi:03d} : ∀ q : SourceTop,
    {offset}≤q.index.val → q.index.val<{offset+count} → ∀ j (p : Fin {h} × ZMod 2),
    frame.symm ((schreierElement q j : Equiv.Perm (Fin {w})) (frame p))=
      (p.1,p.2+schreierBits q j p.1) := by decide +kernel
'''
  module(name,header([root+'SchreierData'],f'pilotSchreierCheck{bi:03d}Group')+body+close)
 schreier_assembly=''
 for theorem,statement in [
  ('nextTop_checked','∀ q j,q*images j=nextTop q j'),
  ('schreier_mem',f'∀ q j,schreierBits q j∈{A}.kernelChart.space'),
  ('schreier_action',f'''∀ q j (p : Fin {h} × ZMod 2),
    frame.symm ((schreierElement q j : Equiv.Perm (Fin {w})) (frame p))=
      (p.1,p.2+schreierBits q j p.1)''')]:
  schreier_assembly+=row_assembly(theorem,statement)
 piece('Schreier',schreier_checks,'pilotSchreierGroup',schreier_assembly)
 piece('Basis',[root+'Base'],'pilotBasisGroup',source_between('private def basisWords','theorem kernel_space'))
 module(root,header([root+'Schreier',root+'Basis'],'pilotAssemblyGroup')+public(whole[whole.index('theorem kernel_space'):]))
 return outputs

def emit_acceptance(node,m,t,binding_module,axis_module=None):
 """Install the independent complete registries on the original action."""
 label=node['id'][1:].replace('_','T');mid=m['id'];sid=t['id']
 A=f'BinaryKernelAxes{mid:03d}';C=f'BinaryKernelCuts{mid:03d}'
 T=f'BinaryTopRegistry{sid:03d}';G=f'BinaryKernelGaps{mid:03d}'
 n=len(m['axes']);q=len(t['normals'])
 faithful=central_data(t,m);central=list(faithful)
 if len(faithful)<len(exceptional_axes(t,m)):
  frame=next(frame for name,frame in m['contexts'] if name==node['id'])
  pair={x:i for i,p in enumerate(frame) for x in p}
  gs=[tuple(x-1 for x in g) for g in node['generators']]
  tops=[tuple(pair[g[p[0]-1]+1] for p in frame) for g in gs]
  section_words=schreier_data(gs,tops,frame,t,m['kernel_basis'])[0]
  complete={x['axis'] for x in central_obstructions(gs,tops,frame,m,t,section_words) if x['complete']}
  central=[entry for entry in central_data(t,m,faithful_only=False)
           if entry in faithful or entry[0] in complete]
 s=f'''import SymmetricSubgroupAsymptotics.BinaryPairSharedAcceptance
import SymmetricSubgroupAsymptotics.BinaryPairCentralKernel
import SymmetricSubgroupAsymptotics.GeneratedPairBindings.{binding_module}
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.Gaps{axis_module or m['batch']}

/-! Complete coverage of every original normal by the shared independent
registries. The exceptional branch identifies the literal original normal
as its coordinate axis; no list of original normal lifts is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairAcceptance{label}
open BinaryPairBinding{label}
local instance : Group SourceTop := BinaryTopSource{sid:03d}.group

private theorem kernel_space : {A}.kernel.toSubmodule=physicalFrame.kernelSpace :=
  BinaryPairBinding{label}.kernel_space.symm

private theorem cells (i : Fin {n}) (j : Fin {q}) :
    ({T}.states j).degree+
      BinaryPairFrame.sharedCost {A}.action {A}.states
        (fun i => {A}.states ({C}.cutIndex i))
        (fun i => {A}.states ({C}.fixedIndex i)) i<Nat.card (Fin 16) ∨
      {G}.exceptionalAxis i ∧ ({T}.states j).kernel=⊥ := by
  have hc : BinaryPairFrame.sharedCost {A}.action {A}.states
      (fun i => {A}.states ({C}.cutIndex i))
      (fun i => {A}.states ({C}.fixedIndex i)) i={C}.cost i :=
    ({C}.cost_eq_actual_finranks i).symm
  simpa only [hc,Nat.card_eq_fintype_card,Fintype.card_fin] using
    {G}.gap_or_trivial_top i j

/-- Every actual original normal has a physical certificate of width 16,
or equals one of the explicit exceptional correlated flip axes. -/
theorem accepted_or_exceptional (N : Subgroup Original) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators physicalFrame.top N,C.width=16) ∨
      ∃ i : Fin {n}, {G}.exceptionalAxis i ∧
        N=physicalFrame.coordinateSubgroup ({A}.states i).toSubmodule := by
  have ht : ∀ T : Subgroup SourceTop,T.Normal → ∃ j,({T}.states j).kernel=T := by
    intro T hT
    letI : T.Normal := hT
    exact {T}.complete T
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
    physicalFrame.shared_complete_acceptance {A}.action topEquiv action_eq
      {A}.kernel kernel_space {A}.states
      (fun i => {A}.states ({C}.cutIndex i))
      (fun i => {A}.states ({C}.fixedIndex i)) {C}.certificate
      {A}.complete {T}.states ht {G}.exceptionalAxis cells generators N

'''
 for ai,di,z in central:
  Z=f'BinaryKernelCentral{mid:03d}.Axis{ai}'
  central_proof=f'''    have hfaith : ∀ g : SourceTop,
        (∀ j,{A}.action g ({A}.kernelChart.inclusion (Pi.single j 1))-
          {A}.kernelChart.inclusion (Pi.single j 1)∈({A}.states {ai}).toSubmodule) → g=1 := by
      simpa only [{A}.states_space] using {Z}.faithful
    have hcentral := physicalFrame.shared_central_quotient_mem_kernel_of_basis
      {A}.action topEquiv action_eq {A}.kernelChart
      BinaryPairBinding{label}.kernel_space.symm ({A}.states {ai}) hfaith
''' if (ai,di,z) in faithful else f'    have hcentral := BinaryPairBinding{label}.centralKernel{ai}\n'
  s+=f'''
def residualAxis{ai} : Subrepresentation physicalFrame.coordinateTopAction :=
  physicalFrame.sharedSubrepresentation {A}.action topEquiv action_eq ({A}.states {ai})
def residualFixed{ai} : Subrepresentation physicalFrame.coordinateTopAction :=
  physicalFrame.sharedSubrepresentation {A}.action topEquiv action_eq ({A}.states {di})
abbrev residualNormal{ai} := physicalFrame.coordinateSubgroup residualAxis{ai}.toSubmodule

/-- Exact central-omega criterion for the literal exceptional original
normal. Its dimension follows from the complete shared fixed preimage. -/
def residualCriterion{ai} : BinaryNormalCharacterCriterion (Original ⧸ residualNormal{ai}) 16 where
  dimension := {z}
  cardinal := by
{central_proof.rstrip()}
    have hfixed := physicalFrame.shared_cut {A}.action topEquiv action_eq
      {A}.kernel ({A}.states {ai}) ({A}.states {ai}) ({A}.states {di}) kernel_space {Z}.certificate
    have hc := physicalFrame.centralOmega_card_of_fixed_chart residualAxis{ai} residualFixed{ai}
      hfixed hcentral
    change Nat.card (binaryCentralOmega (Original ⧸ residualNormal{ai}))=
      2^(Module.finrank (ZMod 2) ({A}.states {di}).toSubmodule-
        Module.finrank (ZMod 2) ({A}.states {ai}).toSubmodule) at hc
    rwa [{Z}.dimension] at hc
  gap := by decide +kernel
'''
 if len(central)==1 and exceptional_axes(t,m)==[central[0][0]]:
  ai=central[0][0]
  s+=f'''
/-- Every original normal has a physical pair certificate or its exact
central-omega character criterion. Analytic character counting is separate. -/
theorem pair_or_character_criterion (N : Subgroup Original) [N.Normal] :
    (∃ C : BinaryPairLocalCertificate generators physicalFrame.top N,C.width=16) ∨
      Nonempty (BinaryNormalCharacterCriterion (Original ⧸ N) 16) := by
  rcases accepted_or_exceptional N with h|⟨i,hi,rfl⟩
  · exact Or.inl h
  · change i={ai} at hi
    subst i
    exact Or.inr ⟨residualCriterion{ai}⟩
'''
 return s+f'end SymmetricSubgroupAsymptotics.BinaryPairAcceptance{label}\n'

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 selection=ap.add_mutually_exclusive_group()
 selection.add_argument('--node',action='append')
 selection.add_argument('--pilot-node',help='Emit isolated PilotBinding/PilotAcceptance files using the corresponding axis Pilot/GapsPilot modules; preserve canonical files and index.')
 ap.add_argument('--check',action='store_true')
 ap.add_argument('--acceptance',action='store_true',help='Also emit original-normal acceptance wrappers, retaining explicit exceptional axes.')
 args=ap.parse_args()
 if args.pilot_node:args.node=[args.pilot_node]
 base=ROOT/'formal/SymmetricSubgroupAsymptotics';ms=json.loads((base/'GeneratedKernelAxes/index.json').read_text());ts=json.loads((base/'GeneratedTopNormals/index.json').read_text())
 with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt') as f:meta=json.loads(next(f))
 nodes={n['id']:n for n in meta['nodes']};seen=set();OUT.mkdir(exist_ok=True);groups={};index=[]
 def write(path,b):
  if args.check:
   if not path.exists() or path.read_bytes()!=b:raise SystemExit(f'Stale generated file {path}')
  elif not path.exists() or path.read_bytes()!=b:path.write_bytes(b)
  print(path.relative_to(ROOT),flush=True)
 for m in ms:
  for name,frame in m['contexts']:
   if args.node and name not in args.node:continue
   if not args.node and nodes[name]['degree']!=16:continue
   assert name not in seen,'Multiple pair frames require explicit context names';seen.add(name)
   axis_module=f'Pilot{m["id"]:03d}' if args.pilot_node else None
   t=ts[m['top_id']];i=next(i for i,c in enumerate(t['contexts']) if c[:2]==[name,frame]);s=emit(nodes[name],frame,m,t,t['bindings'][i],axis_module)
   if args.node:
    label=name[1:].replace('_','T');prefix='Pilot' if args.pilot_node else '';binding_module=f'{prefix}Binding{label}'
    if args.pilot_node:
     for path,body in pilot_modules(nodes[name],m,t,s).items():write(path,body.encode())
    else:write(OUT/f'{binding_module}.lean',s.encode())
    if args.acceptance:
     write(OUT/f'{prefix}Acceptance{label}.lean',emit_acceptance(nodes[name],m,t,binding_module,axis_module).encode())
   else:
    groups.setdefault(m['batch'],[]).append((name,m,s))
 if args.node and set(args.node)!=seen:
  raise SystemExit(f'No unique shared context for requested nodes: {sorted(set(args.node)-seen)}')
 if not args.node:
  number=0
  for axis_batch,entries in sorted(groups.items()):
   for start in range(0,len(entries),48):
    selected=entries[start:start+48];imports=set();bodies=[];batch=f'Batch{number:03d}';number+=1
    for name,m,s in selected:
     lines=s.splitlines();imports.update(line for line in lines if line.startswith('import '))
     bodies.append('\n'.join(line for line in lines if not line.startswith(('import ','set_option ','noncomputable section'))))
     index.append({'node':name,'axis':m['id'],'top':m['top_id'],'axis_batch':axis_batch,'batch':batch})
     label=name[1:].replace('_','T')
     write(OUT/f'Binding{label}.lean',f'import SymmetricSubgroupAsymptotics.GeneratedPairBindings.{batch}\n'.encode())
     if args.acceptance:
      write(OUT/f'Acceptance{label}.lean',f'import SymmetricSubgroupAsymptotics.GeneratedPairBindings.Acceptance{batch}\n'.encode())
    result='\n'.join(sorted(imports))+'\n\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false\nnoncomputable section\n'+'\n'.join(bodies)
    write(OUT/(batch+'.lean'),result.encode())
    if args.acceptance:
     acceptance_imports=set();acceptance_bodies=[]
     for name,m,_ in selected:
      lines=emit_acceptance(nodes[name],m,ts[m['top_id']],batch).splitlines()
      acceptance_imports.update(line for line in lines if line.startswith('import '))
      acceptance_bodies.append('\n'.join(line for line in lines if not line.startswith(('import ','set_option ','noncomputable section'))))
     result='\n'.join(sorted(acceptance_imports))+'\n\nset_option autoImplicit false\nnoncomputable section\n'+'\n'.join(acceptance_bodies)
     write(OUT/('Acceptance'+batch+'.lean'),result.encode())
  write(OUT/'index.json',(json.dumps(index,indent=2)+'\n').encode())
if __name__=='__main__':main()
