import SymmetricSubgroupAsymptotics.CFSGE6PositiveRootLowerWitness
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOrderLower
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding

/-! The small-index E6 branch forces the literal field to have two
elements. The proof uses only a positive-root lower witness, the proved
original order lower bound, and the actual faithful coset action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6SmallIndexField
open CFSG.Models.Chevalley CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormalizerWordIdentity CFSGSignedCartanReflections
open CFSGNormTwoCoordinateOriginalRootFamily CFSGNormTwoCoordinateOriginalOrderLower
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGE6PositiveRootLowerWitness
open PrimitiveSocleRawStructure
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

/-- A lower bound, rather than an imported exceptional order formula. -/
theorem serreTypeE6_order_lower (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)] :
    Nat.card K ^ 72 ≤ Nat.card (Projective CartanMatrix.E₆ K) := by
  have hC := E6_cartan
  change cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) = CartanMatrix.E₆ at hC
  letI : IsSimpleGroup (Projective (cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)) K) := by
    rw [hC]
    infer_instance
  have h := original_card_lower CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K E6Signs E6_signs_square E6_signs_cartan
    (E6_normalizer_word_identity K) p 0
  have hn := positive_root_card_lower
  have hq : 1 ≤ Nat.card K := (Finite.one_lt_card (α := K)).le
  have hpow : Nat.card K ^ 72 ≤ Nat.card K ^ (2 * Nat.card (PositiveRoot CartanMatrix.E₆)) :=
    Nat.pow_le_pow_right hq (by omega)
  simpa only [hC] using hpow.trans h

private theorem e6_projective_finite (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.E₆ K)] : Finite (Projective CartanMatrix.E₆ K) := by
  have hC := E6_cartan
  change cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) = CartanMatrix.E₆ at hC
  letI : IsSimpleGroup (Projective (cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)) K) := by
    rw [hC]
    infer_instance
  have h := original_projective_finite CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 0
  simpa only [hC] using h

theorem field_card_eq_two_of_index_lt_twentySeven (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)]
    (ell : ℕ) (hell : LeastProperIndex (Projective CartanMatrix.E₆ K) ell) (hlt : ell < 27) :
    Nat.card K = 2 := by
  letI := e6_projective_finite K
  obtain ⟨H,hH,hi⟩ := hell.1
  have hupper : Nat.card (Projective CartanMatrix.E₆ K) ≤ (26 : ℕ).factorial := by
    exact (simple_card_le_index_factorial H hH).trans (Nat.factorial_le (by omega))
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  by_contra hne
  have hthree : 3 ≤ Nat.card K := by omega
  have hlower : 3 ^ 72 ≤ Nat.card (Projective CartanMatrix.E₆ K) :=
    (Nat.pow_le_pow_left hthree 72).trans (serreTypeE6_order_lower K p)
  have hnum : (26 : ℕ).factorial < 3 ^ 72 := by decide
  omega

end SymmetricSubgroupAsymptotics.CFSGE6SmallIndexField
