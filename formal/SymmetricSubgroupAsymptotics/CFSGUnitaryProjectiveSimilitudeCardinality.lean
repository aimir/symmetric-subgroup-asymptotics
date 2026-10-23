import SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudePointAction
import SymmetricSubgroupAsymptotics.CFSGUnitaryMatrixCardinalityBounds

/-! The projective image of ALL actual signed-unitary similitudes
has cardinality at most the literal natural special fixed group. The
full quadratic-field scalar kernel cancels both multiplier and
determinant factors, without a unitary order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianSimilitudeGroup

theorem unitary_similitude_pointImage_card_le_naturalFixed
    (q : CFSG.PrimePower) (r : ℕ) :
    Nat.card (singularPointHom (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) r)).range ≤
        Nat.card (CFSGTwistedAUpperUnipotent.naturalFixed r q) := by
  apply singularPointImage_card_le_of_scalar_bound
  have hh := unitary_linearSimilitudes_card_le q r
  have hc : Nat.card (q.Extension 2) = q.order ^ 2 := by
    change Nat.card (GaloisField q.prime (2 * q.exponent)) = (q.prime ^ q.exponent) ^ 2
    rw [GaloisField.card q.prime (2 * q.exponent) (by have := q.exponent_pos; omega),
      ← pow_mul, Nat.mul_comm q.exponent 2]
  simpa only [Nat.card_units, hc] using hh

theorem unitary_similitude_pointImage_card_le_original_mul_dimension
    (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (singularPointHom (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (s + 3))).range ≤
        (s + 4) * Nat.card (CFSG.Models.TwistedA (s + 3) q) :=
  (unitary_similitude_pointImage_card_le_naturalFixed q (s + 3)).trans
    (unitary_naturalFixed_card_le_projective_mul_dimension q s)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
