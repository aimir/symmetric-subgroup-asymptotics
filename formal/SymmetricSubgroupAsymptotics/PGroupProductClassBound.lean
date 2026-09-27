import SymmetricSubgroupAsymptotics.SubgroupProductClassBound
import Mathlib.GroupTheory.PGroup

/-! A p-group specialization of the correlated-product class bound.
Only actual p-subgroups of the original ambient coordinates need class
bounds. Each coordinate is first restricted to its actual image of the
original p-group, so every subgroup used in the kernel filtration remains
a p-group. The ambient coordinate groups themselves need not be p-groups.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

universe u v w

/-- Uniform bounds on only the p-subgroups of the original coordinates
control a finite original p-group with jointly injective coordinate maps. -/
theorem pGroup_conjugacyClass_card_le_finite_coordinate_bounds
    (p : ℕ) {ι : Type v} [Fintype ι]
    (V : ι → Type u) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (c : ι → ℕ)
    (hc : ∀ i (L : Subgroup (V i)), IsPGroup p L →
      Nat.card (ConjClasses L) ≤ c i)
    (H : Type w) [Group H] [Finite H] (hH : IsPGroup p H)
    (f : ∀ i, H →* V i)
    (hf : Function.Injective (fun h i => f i h)) :
    Nat.card (ConjClasses H) ≤ ∏ i, c i := by
  let image : ι → Type u := fun i => (f i).range
  let restricted : ∀ i, H →* image i := fun i => (f i).rangeRestrict
  have himage : ∀ i, IsPGroup p (image i) := fun i =>
    hH.of_surjective (f i).rangeRestrict (f i).rangeRestrict_surjective
  have hrestricted : Function.Injective (fun h i => restricted i h) := by
    intro x y h
    apply hf
    funext i
    exact congrArg (fun z : (f i).range => (z : V i)) (congrFun h i)
  have hbound : ∀ i (L : Subgroup (image i)),
      Nat.card (ConjClasses L) ≤ c i := by
    intro i L
    let M : Subgroup (V i) := L.map (f i).range.subtype
    let e : L ≃* M := L.equivMapOfInjective
      (f i).range.subtype Subtype.coe_injective
    have hL : IsPGroup p L := (himage i).to_subgroup L
    have hM : IsPGroup p M := hL.of_equiv e
    have hclasses : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses M) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    exact hclasses.trans (hc i M hM)
  exact conjugacyClass_card_le_finite_coordinate_bounds
    image c hbound H restricted hrestricted

/-- The literal product-subgroup form; only p-subgroups of its original
coordinate groups appear in the supplied finite base. -/
theorem pGroup_subgroupProduct_conjugacyClass_card_le
    (p : ℕ) {ι : Type v} [Fintype ι]
    (V : ι → Type u) [∀ i, Group (V i)] [∀ i, Finite (V i)]
    (H : Subgroup (∀ i, V i)) (hH : IsPGroup p H) (c : ι → ℕ)
    (hc : ∀ i (L : Subgroup (V i)), IsPGroup p L →
      Nat.card (ConjClasses L) ≤ c i) :
    Nat.card (ConjClasses H) ≤ ∏ i, c i := by
  let f : ∀ i, H →* V i :=
    fun i => (Pi.evalMonoidHom V i).comp H.subtype
  apply pGroup_conjugacyClass_card_le_finite_coordinate_bounds p V c hc H hH f
  intro x y h
  apply Subtype.ext
  exact h

/-- In particular an original p-group inside `n` correlated copies of `G`
has at most `c^n` classes when every actual p-subgroup of `G` has at most `c`.
The finite base can include intransitive p-subgroups of a permutation group. -/
theorem pGroup_subgroupPower_conjugacyClass_card_le
    (p : ℕ) (G : Type u) [Group G] [Finite G] (n c : ℕ)
    (hc : ∀ L : Subgroup G, IsPGroup p L → Nat.card (ConjClasses L) ≤ c)
    (H : Subgroup (Fin n → G)) (hH : IsPGroup p H) :
    Nat.card (ConjClasses H) ≤ c ^ n := by
  simpa using pGroup_subgroupProduct_conjugacyClass_card_le p
    (fun _ : Fin n => G) H hH (fun _ => c) (fun _ => hc)

end SymmetricSubgroupAsymptotics

end
