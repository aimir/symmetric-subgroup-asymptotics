import SymmetricSubgroupAsymptotics.FiniteNormalizerCardDivisor
import SymmetricSubgroupAsymptotics.PrimitiveSocleCentralizerRegular

/-! A faithful transitive abelian subgroup equals the order of its
centralizer on the original points. Its normalizer order therefore divides
the action degree times its actual automorphism order. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

theorem centralizer_card_of_abelian_transitive
    {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [FaithfulSMul G X] (H : Subgroup G)
    [MulAction.IsPretransitive H X] (hcomm : IsMulCommutative H) :
    Nat.card (Subgroup.centralizer (H : Set G)) = Nat.card X := by
  let x : X := Classical.choice inferInstance
  let C := Subgroup.centralizer (H : Set G)
  let eval : C → X := fun c => c • x
  have heval : Function.Injective eval := by
    intro a b hab
    have he : a⁻¹*b = 1 :=
      PrimitiveSocleONanScottHelpers.centralizer_free H x (a⁻¹*b) (by
        change a • x = b • x at hab
        rw [mul_smul,←hab,inv_smul_smul])
    exact inv_mul_eq_one.mp he
  have hupper : Nat.card C ≤ Nat.card X := Nat.card_le_card_of_injective eval heval
  have hH : Nat.card H = Nat.card X := Nat.card_congr
    (PrimitiveSocleONanScottHelpers.regularPointEquiv H
      (PrimitiveSocleONanScottHelpers.abelian_transitive_regular H hcomm) x)
  have hle : H ≤ C := Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm
  have hlower : Nat.card H ≤ Nat.card C := Nat.card_le_card_of_injective
    (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  change Nat.card C = Nat.card X
  rw [hH] at hlower
  exact Nat.le_antisymm hupper hlower

theorem normalizer_card_dvd_degree_mul_aut_of_abelian_transitive
    {G X : Type} [Group G] [Finite G] [Finite X] [Nonempty X]
    [MulAction G X] [FaithfulSMul G X] (H : Subgroup G)
    [MulAction.IsPretransitive H X] (hcomm : IsMulCommutative H) :
    Nat.card (Subgroup.normalizer (H : Set G)) ∣ Nat.card X * Nat.card (MulAut H) := by
  simpa only [centralizer_card_of_abelian_transitive (X := X) H hcomm] using
    normalizer_card_dvd_centralizer_mul_aut H

end SymmetricSubgroupAsymptotics
