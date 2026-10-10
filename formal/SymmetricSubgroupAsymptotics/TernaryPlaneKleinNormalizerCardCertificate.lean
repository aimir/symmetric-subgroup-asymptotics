import SymmetricSubgroupAsymptotics.TernaryPlaneKleinPair

/-!
# Finite cardinal certificate for ternary Klein normalizers

This module contains only the finite calculation showing that the
normalizer of a displayed independent commuting involution pair in
`GL₂(3)` has order eight.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

/-- The computable normalizer filter has eight elements for every
independent commuting involution pair.  Unlike `Nat.card` of a subgroup,
this statement reduces only the explicit `Finset` enumerator. -/
set_option maxRecDepth 100000 in
theorem kleinNormalizerFinset_card_eq_eight_certificate :
    ∀ a b : GL3,
      a ≠ 1 → b ≠ 1 → a ≠ b →
      a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
      (kleinNormalizerFinset a b).card = 8 := by
  decide +kernel

/-- Bridge the computable filter cardinal to the actual subgroup
normalizer. -/
theorem pair_normalizer_card_eq_eight_certificate
    (a b : GL3)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hcomm : a * b = b * a) :
    Nat.card (Subgroup.normalizer (kleinPairSubgroup a b : Set GL3)) = 8 := by
  let e :
      Subgroup.normalizer (kleinPairSubgroup a b : Set GL3) ≃
        {g : GL3 // g ∈ kleinNormalizerFinset a b} :=
    { toFun := fun g =>
        ⟨g.1, (mem_kleinNormalizerFinset_iff a b g.1 ha2 hb2 hcomm).mpr g.2⟩
      invFun := fun g =>
        ⟨g.1, (mem_kleinNormalizerFinset_iff a b g.1 ha2 hb2 hcomm).mp g.2⟩
      left_inv := fun g => Subtype.ext rfl
      right_inv := fun g => Subtype.ext rfl }
  calc
    Nat.card (Subgroup.normalizer (kleinPairSubgroup a b : Set GL3)) =
        Nat.card {g : GL3 // g ∈ kleinNormalizerFinset a b} :=
      Nat.card_congr e
    _ = (kleinNormalizerFinset a b).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = 8 := kleinNormalizerFinset_card_eq_eight_certificate
      a b ha hb hab ha2 hb2 hcomm

end LinearThree
end SymmetricSubgroupAsymptotics

end
