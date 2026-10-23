import SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionFibres
import Mathlib.Data.Fintype.Card

/-! Each full cycle partition has at most two actual alternating
conjugacy classes, and at most one unless its parts are distinct and odd.
These bounds concern literal class fibres; no class-count formula or
assumed list of conjugacy types is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionFibreBounds
open Equiv Equiv.Perm AlternatingConjugacyPartitionFibres
variable {I:Type*}[Fintype I][DecidableEq I]

abbrev Fibre (p:Nat.Partition (Fintype.card I)) :=
  {c:ConjClasses (alternatingGroup I) // classPartition c=p}

theorem fibre_card_le_two (t:Perm I)(ht:sign t= -1)(p:Nat.Partition (Fintype.card I)) :
    Nat.card (Fibre (I:=I) p)≤2 := by
  by_cases hn:Nonempty (Fibre (I:=I) p)
  · let c₀:Fibre (I:=I) p:=Classical.choice hn
    let a:=representative c₀.val
    have ha:a.val.partition=p := c₀.property
    let c₁:Fibre (I:=I) p:=⟨ConjClasses.mk (oddConjugate t a),by
      rw [classPartition_mk]
      have hc:IsConj a.val (oddConjugate t a).val := isConj_iff.mpr ⟨t,rfl⟩
      exact (Perm.partition_eq_of_isConj.mp hc).symm.trans ha⟩
    let f:Fin 2→Fibre (I:=I) p:=fun i=>if i=0 then c₀ else c₁
    have hf:Function.Surjective f := by
      intro c
      let b:=representative c.val
      have hb:b.val.partition=p := c.property
      have hs:IsConj a.val b.val := Perm.partition_eq_of_isConj.mpr (ha.trans hb.symm)
      rcases odd_conjugate_cover t ht a b hs with hh|hh
      · have he:c₀.val=c.val := (mk_representative c₀.val).symm.trans
          ((ConjClasses.mk_eq_mk_iff_isConj.mpr hh).trans (mk_representative c.val))
        refine ⟨0,?_⟩
        change (if (0:Fin 2)=0 then c₀ else c₁)=c
        rw [if_pos rfl]
        exact Subtype.ext he
      · have he:c₁.val=c.val :=
          (ConjClasses.mk_eq_mk_iff_isConj.mpr hh).trans (mk_representative c.val)
        refine ⟨1,?_⟩
        change (if (1:Fin 2)=0 then c₀ else c₁)=c
        rw [if_neg (by decide)]
        exact Subtype.ext he
    simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf
  · letI : IsEmpty (Fibre (I:=I) p) := ⟨fun c=>hn ⟨c⟩⟩
    simp

theorem fibre_card_le_one (p:Nat.Partition (Fintype.card I))
    (hp:¬(p.parts.Nodup ∧ ∀a∈p.parts,Odd a)) : Nat.card (Fibre (I:=I) p)≤1 := by
  have hsub:∀c d:Fibre (I:=I) p,c=d := by
    intro c d
    let a:=representative c.val
    let b:=representative d.val
    have ha:a.val.partition=p := c.property
    have hb:b.val.partition=p := d.property
    have hh:IsConj a b := nonsplit_isConj a b (ha.trans hb.symm) (by simpa only [ha] using hp)
    apply Subtype.ext
    exact (mk_representative c.val).symm.trans
      ((ConjClasses.mk_eq_mk_iff_isConj.mpr hh).trans (mk_representative d.val))
  have hi:Function.Injective (fun _:Fibre (I:=I) p=>(0:Fin 1)) := fun c d _=>hsub c d
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ hi

theorem partition_even (c:ConjClasses (alternatingGroup I)) :
    Even (Fintype.card I+(classPartition c).parts.card) := by
  let g:=representative c
  have hs:g.val.sign=1 := g.property
  rw [Perm.sign_of_cycleType,neg_one_pow_eq_one_iff_even (by simp)] at hs
  have hc:g.val.cycleType.sum+(Fintype.card I-g.val.support.card)=Fintype.card I := by
    rw [Perm.sum_cycleType]
    have hl:=Finset.card_le_univ g.val.support
    omega
  change Even (Fintype.card I+g.val.partition.parts.card)
  rw [Perm.parts_partition,Multiset.card_add,Multiset.card_replicate]
  have hh:=hs.add (show Even ((Fintype.card I-g.val.support.card)+(Fintype.card I-g.val.support.card)) from ⟨_,rfl⟩)
  convert hh using 1; omega

end SymmetricSubgroupAsymptotics.AlternatingConjugacyPartitionFibreBounds
