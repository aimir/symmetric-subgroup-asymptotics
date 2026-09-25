#!/usr/bin/env python3
"""Export every width-8 pair local certificate against actual normal rows.
K, K∩N, the selected original cut, its full fixed preimage, and KN are
identified with existing checked original normal states. Their exact group
orders give the numerical cut/fixed dimensions. Cover maps retain the
original source-generator images. No capacity is a checker premise.
"""
from pathlib import Path
import argparse,gzip,json
from export_lean_menu_cayley import table,packed,lookup,checks,compose
from export_lean_normal_registry import action_data,unpack,perm,arr,inv,finfun
ROOT=Path(__file__).resolve().parents[2];OUT=ROOT/'formal/SymmetricSubgroupAsymptotics/GeneratedPair8'

def word(t,i):
    if i==t['identity']:return []
    return word(t,t['parent'][i])+[t['letter'][i]]

def emit(node,record):
 label=node['id'][1:].replace('_','T');gs,st,source,si,ns=action_data(node,record);n=len(source);d=len(gs);m=len(ns);NF=f'BinaryNormal{label}';FF=f'BinaryPair{label}.Frame0'
 ni={frozenset(x['ns']):i for i,x in enumerate(ns)}
 masks=[sum(1<<j for j in x['source_indices']) for x in ns]
 pairs=[(i,x) for i,x in enumerate(ns) if x['record']['kind']=='pair']
 def groupkey(rows):return frozenset(unpack(c,8) for c in table(list(map(perm,rows)),8)['codes'])
 ki=ni[groupkey(pairs[0][1]['record']['kernel_generators'])];ks=ns[ki]['ns']
 s=f'''import SymmetricSubgroupAsymptotics.BinaryPairFiniteRows
import SymmetricSubgroupAsymptotics.GeneratedNormal8.Registry{label}
import SymmetricSubgroupAsymptotics.GeneratedPair8.Frames{label}

/-! All pair-type normal states of {label}: original cuts, complete fixed
preimages, quotient covers and exact local gaps. All finite equations use
the Lean kernel. Character and transport records are separate branches. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairLocal{label}
abbrev Source := FiniteGroupRow {n}
local instance : Group Source := BinaryMenuCayley{label}.group
abbrev generators := {NF}.generators
abbrev top := {FF}.topHom
private def mask (i : Fin {m}) : ℕ := {lookup(masks)}
private abbrev member (i : Fin {m}) (x : Source) : Prop := mask i / 2^x.index.val % 2=1

private theorem member_iff (i : Fin {m}) (x : Source) :
    member i x ↔ x∈({NF}.states i).kernel := by
  fin_cases i
'''
 for i,nd in enumerate(ns):
  k=len(nd['ns']);s+=f'''  · change member {i} x ↔ x∈Subgroup.closure (Set.range {NF}.N{i}.normalGenerators)
    rw [binaryNormalRow_mem_iff {NF}.N{i}.normalCertificate]
    have h : ∀ z : Fin {n}, member {i} ⟨z⟩ ↔ ∃ j : Fin {k}, {NF}.N{i}.normalCertificate.rows j=z := {checks(n)}
    exact h x.index
'''
 s+=f'''
theorem kernel_eq : top.ker={NF}.N{ki}.kernel := by
  ext x
  change top x=1 ↔ x∈({NF}.states {ki}).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, top x=1 ↔ member {ki} x from by decide +kernel) x

'''
 for i,nd in pairs:
  rec=nd['record'];nset=set(nd['ns']);mi=ni[frozenset(set(ks)&nset)];ci=ni[groupkey(rec['cut_lift_generators'])];cs=set(ns[ci]['ns'])
  ds=frozenset(x for x in ks if all(compose(inv(x),compose(compose(g,x),inv(g))) in cs for g in gs));di=ni[ds]
  kn=frozenset(compose(k,x) for k in ks for x in nd['ns']);bi=ni[kn]
  c=rec['c'];r=rec['r'];cv=rec['cover_degree'];assert len(ns[ci]['ns'])==len(ns[mi]['ns'])*2**c;assert len(ns[di]['ns'])==len(ns[ci]['ns'])*2**r
  assert cv+2*c+4*r<8
  cg=list(map(perm,rec['cut_lift_generators']));ct=table(cg,8);ctperm=[unpack(v,8) for v in ct['codes']];cw=[word(ct,ctperm.index(g)) for g in ns[ci]['ng']];cgidx=[si[g] for g in cg];cr=len(cg);cgr=len(ns[ci]['ng'])
  kvals=[];nvals=[]
  for g in ns[bi]['ng']:
   k=next(k for k in ks if compose(inv(k),g) in nset);kvals.append(si[k]);nvals.append(si[compose(inv(k),g)])
  br=len(ns[bi]['ng'])
  ims=list(map(perm,rec['cover_images']));values=[None]*n;values[st['identity']]=tuple(range(cv))
  for j in sorted(range(n),key=lambda j:st['rank'][j]):
   if j!=st['identity']:values[j]=compose(values[st['parent'][j]],ims[st['letter'][j]])
  targets=sorted(set(values),key=packed); vi=[targets.index(x) for x in values];gi=[targets.index(x) for x in ims]
  s+=f'''namespace N{i}

theorem intersection_eq : top.ker⊓{NF}.N{i}.kernel={NF}.N{mi}.kernel := by
  rw [kernel_eq]
  ext x
  change (x∈({NF}.states {ki}).kernel ∧ x∈({NF}.states {i}).kernel) ↔ x∈({NF}.states {mi}).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member {ki} x ∧ member {i} x) ↔ member {mi} x from by decide +kernel) x

theorem cut_le : {NF}.N{ci}.kernel≤top.ker := by
  intro x hx
  have hk : x∈{NF}.N{ki}.kernel := (member_iff {ki} x).mp
    ((show ∀ x : Source, member {ci} x → member {ki} x from by decide +kernel) x ((member_iff {ci} x).mpr hx))
  exact kernel_eq.symm ▸ hk

theorem intersection_le : top.ker⊓{NF}.N{i}.kernel≤{NF}.N{ci}.kernel := by
  intro x hx
  have hx' : x∈{NF}.N{mi}.kernel := intersection_eq ▸ hx
  apply (member_iff {ci} x).mp
  exact (show ∀ x : Source, member {mi} x → member {ci} x from by decide +kernel) x ((member_iff {mi} x).mpr hx')

theorem cut_central : ∀ j, ∀ x : {NF}.N{ci}.kernel,
    (x:Source)⁻¹*(generators j*(x:Source)*(generators j)⁻¹)∈{NF}.N{i}.kernel := by
  have h : ∀ j, ∀ x : Source, member {ci} x →
      member {i} (x⁻¹*(generators j*x*(generators j)⁻¹)) := by decide +kernel
  intro j x
  exact (member_iff {i} _).mp (h j x.val ((member_iff {ci} x.val).mpr x.property))

theorem fixed_eq : binaryPairFixedSubgroup top.ker {NF}.N{ci}.kernel={NF}.N{di}.kernel := by
  rw [kernel_eq]
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ generators {NF}.generators_full]
  change (x∈({NF}.states {ki}).kernel ∧ ∀ j,
    x⁻¹*(generators j*x*(generators j)⁻¹)∈({NF}.states {ci}).kernel) ↔ x∈({NF}.states {di}).kernel
  simp only [← member_iff]
  exact (show ∀ x : Source, (member {ki} x ∧ ∀ j,
    member {ci} (x⁻¹*(generators j*x*(generators j)⁻¹))) ↔ member {di} x from by decide +kernel) x

'''
  cgexpr=f'⟨{finfun(cgidx,n,"j.val")}⟩' if cr else 'Fin.elim0 j';cwexpr=lookup([f'({str(w)} : List (Fin {cr}))' for w in cw],'j.val') if cgr else 'Fin.elim0 j'
  s+=f'''/-- These are the actual selected cut lift generators from this record. -/
def recordedCutGenerators (j : Fin {cr}) : Source := {cgexpr}
private def cutWords (j : Fin {cgr}) : List (Fin {cr}) := {cwexpr}
private theorem cutWords_checked : ∀ j,
    ((cutWords j).map recordedCutGenerators).prod={NF}.N{ci}.normalGenerators j := by decide +kernel

theorem recorded_cut_eq : Subgroup.closure (Set.range recordedCutGenerators)={NF}.N{ci}.kernel := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact (member_iff {ci} _).mp
      ((show ∀ j, member {ci} (recordedCutGenerators j) from by decide +kernel) j)
  · exact (BinaryNormalGeneratorWords.closure_le
      ({{words := cutWords, equations := cutWords_checked}} :
        BinaryNormalGeneratorWords {NF}.N{ci}.normalGenerators recordedCutGenerators))

'''
  kexpr=f'⟨{finfun(kvals,n,"j.val")}⟩' if br else 'Fin.elim0 j'; nexpr=f'⟨{finfun(nvals,n,"j.val")}⟩' if br else 'Fin.elim0 j'
  s+=f'''private def kernelPart (j : Fin {br}) : Source := {kexpr}
private def normalPart (j : Fin {br}) : Source := {nexpr}

theorem join_eq : top.ker⊔{NF}.N{i}.kernel={NF}.N{bi}.kernel := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      have hx' : x∈{NF}.N{ki}.kernel := kernel_eq ▸ hx
      exact (member_iff {bi} x).mp
        ((show ∀ x : Source, member {ki} x → member {bi} x from by decide +kernel) x ((member_iff {ki} x).mpr hx'))
    · intro x hx
      exact (member_iff {bi} x).mp
        ((show ∀ x : Source, member {i} x → member {bi} x from by decide +kernel) x ((member_iff {i} x).mpr hx))
  · change Subgroup.closure (Set.range {NF}.N{bi}.normalGenerators)≤_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    have he : ∀ j, kernelPart j*normalPart j={NF}.N{bi}.normalGenerators j := by decide +kernel
    rw [← he j]
    apply Subgroup.mul_mem
    · apply (show top.ker≤top.ker⊔{NF}.N{i}.kernel from le_sup_left)
      rw [kernel_eq]
      exact (member_iff {ki} _).mp ((show ∀ j, member {ki} (kernelPart j) from by decide +kernel) j)
    · apply (show {NF}.N{i}.kernel≤top.ker⊔{NF}.N{i}.kernel from le_sup_right)
      exact (member_iff {i} _).mp ((show ∀ j, member {i} (normalPart j) from by decide +kernel) j)

'''
  for z,t in enumerate(targets):
   if cv:
    s+=f'''private def cover{z} : Equiv.Perm (Fin {cv}) where
  toFun x := ({arr(t)} : Array (Fin {cv}))[x.val]!
  invFun x := ({arr(inv(t))} : Array (Fin {cv}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
'''
   else:s+=f'''private def cover{z} : Equiv.Perm (Fin 0) where
  toFun := Fin.elim0
  invFun := Fin.elim0
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x
'''
  s+=f'''
private def coverValues (i : Fin {n}) : Equiv.Perm (Fin {cv}) := {lookup([f'cover{x}' for x in vi])}
private def coverImages (j : Fin {d}) : Equiv.Perm (Fin {cv}) := {lookup([f'cover{x}' for x in gi],'j.val')}
private theorem cover_step : ∀ i j,
    coverValues (BinaryMenuCayley{label}.certificate.next i j)=coverValues i*coverImages j := {checks(n)}
private theorem cover_identity : coverValues BinaryMenuCayley{label}.certificate.identity=1 := by decide +kernel

def cover : Source →* Equiv.Perm (Fin {cv}) where
  toFun x := coverValues x.index
  map_one' := cover_identity
  map_mul' x y := by
    change coverValues (BinaryMenuCayley{label}.certificate.walk x.index
      (BinaryMenuCayley{label}.certificate.words y.index))=coverValues x.index*coverValues y.index
    rw [EncodedCayleyCertificate.values_walk _ coverValues coverImages cover_step,
      ← EncodedCayleyCertificate.values_word _ coverValues coverImages cover_step cover_identity]

theorem cover_kernel : cover.ker=top.ker⊔{NF}.N{i}.kernel := by
  rw [join_eq]
  ext x
  change cover x=1 ↔ x∈({NF}.states {bi}).kernel
  rw [← member_iff]
  exact (show ∀ x : Source, cover x=1 ↔ member {bi} x from by decide +kernel) x

/-- Every local numerical dimension follows from checked original subgroup
orders and maps; the selected original cut and full fixed preimage remain. -/
def certificate : BinaryPairLocalCertificate generators top {NF}.N{i}.kernel where
  cut := {NF}.N{ci}.kernel
  cut_normal := inferInstance
  cut_le_kernel := cut_le
  intersection_le_cut := intersection_le
  central := cut_central
  cutDimension := {c}
  fixedDimension := {r}
  cut_card := by simp only [intersection_eq,{NF}.N{ci}.kernel_card,{NF}.N{mi}.kernel_card] <;> decide
  fixed_card := by simp only [fixed_eq,{NF}.N{di}.kernel_card,{NF}.N{ci}.kernel_card] <;> decide
  coverDegree := {cv}
  cover := cover
  cover_kernel := cover_kernel
  width := 8
  gap := by decide

end N{i}

'''
 s+=f'end SymmetricSubgroupAsymptotics.BinaryPairLocal{label}\n';return OUT/f'Local{label}.lean',s

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--node',action='append');ap.add_argument('--check',action='store_true');args=ap.parse_args()
 with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt') as f:
  meta=json.loads(next(f));records={x['id']:x for line in f if (x:=json.loads(line)).get('kind')=='action'}
 nodes={n['id']:n for n in meta['nodes']}; names=args.node or [k for k,n in nodes.items() if n['degree']==8 and any(r['kind']=='pair' for r in records[k]['normals'])]
 OUT.mkdir(exist_ok=True)
 for name in names:
  p,s=emit(nodes[name],records[name]);b=s.encode()
  if args.check:
   if not p.exists() or p.read_bytes()!=b:raise SystemExit(f'Stale generated file {p}')
  elif not p.exists() or p.read_bytes()!=b:p.write_bytes(b)
  print(p.relative_to(ROOT))
if __name__=='__main__':main()
