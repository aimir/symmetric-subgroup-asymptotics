import SymmetricSubgroupAsymptotics.IndexTwoConjugacyClassCount
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A centralizer projection on a normal subgroup controls its full
ambient centralizer with the actual subgroup index as multiplier. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NormalSubgroupCentralizerProjection

variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (K : Subgroup G) [K.Normal] (f : K →* H)
    (hinj : ∀ x : G, x ∉ K → ∀ y z : K,
      Commute x (y : G) → Commute x (z : G) → f y = f z → y = z)

omit [Finite G] [K.Normal] in
include hinj in
theorem kernel_partner_card_le (x : G) (hx : x ∉ K) :
    Nat.card {y : K // Commute x (y : G)} ≤ Nat.card H := by
  apply Nat.card_le_card_of_injective (fun y : {y : K // Commute x (y : G)} => f y.1)
  intro y z he
  exact Subtype.ext (hinj x hx y.1 z.1 y.2 z.2 he)

include hinj in
theorem whole_partner_card_le (x : G) (hx : x ∉ K) :
    Nat.card {y : G // Commute x y} ≤ K.index * Nat.card H := by
  let C : Subgroup G := Subgroup.centralizer {x}
  let q : C →* G ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  let into : q.ker → H := fun y => f ⟨((y : C) : G),by
    have hy : QuotientGroup.mk' K (((y : C) : G))=1 := y.property
    exact (QuotientGroup.eq_one_iff _).mp hy⟩
  have hi : Function.Injective into := by
    intro a b hab
    have ha : Commute x (((a : C) : G)) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (a : C).property).symm
    have hb : Commute x (((b : C) : G)) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (b : C).property).symm
    have he := hinj x hx _ _ ha hb hab
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun z : K => (z : G)) he)
  have hk : Nat.card q.ker ≤ Nat.card H := Nat.card_le_card_of_injective into hi
  have hr : Nat.card q.range ≤ K.index := by
    have h := Nat.card_le_card_of_injective
      (q.range.subtype : q.range → G ⧸ K) Subtype.val_injective
    exact h
  have heq : Nat.card C = Nat.card q.ker * Nat.card q.range := by
    simpa only [Subgroup.index_ker] using q.ker.card_mul_index.symm
  have hc : Nat.card {y : G // Commute x y} = Nat.card C := by
    apply Nat.card_congr
    exact {
      toFun := fun y => ⟨y.1,Subgroup.mem_centralizer_singleton_iff.mpr y.2.eq.symm⟩
      invFun := fun y => ⟨y.1,(Subgroup.mem_centralizer_singleton_iff.mp y.2).symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hc,heq]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul hk hr

end SymmetricSubgroupAsymptotics.NormalSubgroupCentralizerProjection
