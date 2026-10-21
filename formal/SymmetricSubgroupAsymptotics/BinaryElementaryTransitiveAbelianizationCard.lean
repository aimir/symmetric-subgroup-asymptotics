import SymmetricSubgroupAsymptotics.ElementaryBinaryTransitiveNormalRank
import Mathlib.GroupTheory.Abelianization.Defs

/-! An actual faithful transitive exponent-two action is regular, and
its full abelianization has the same order as the original point set. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem binary_elementary_transitive_abelianization_card
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X]
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := U) (X := X)) (x : X) :
    Nat.card (Abelianization U) = Nat.card X := by
  have hpow := BinarySquareActionStructure.squaresActTrivially_iff_pow_two.mp hel
  letI : IsMulCommutative U := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun g => orderOf_dvd_iff_pow_eq_one.mpr (hpow g)) a b).eq⟩⟩
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator U)
  have hd : Nat.card (commutator U) = 1 := by
    rw [commutator_eq_bot,Subgroup.card_bot]
  change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hc
  rw [hd,mul_one] at hc
  exact hc.symm.trans (ElementaryBinaryTransitiveNormalRank.card_eq_degree hel x)

end SymmetricSubgroupAsymptotics
