import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicTripleBridge
import SymmetricSubgroupAsymptotics.CFSGTwistedDDoubleTailEmbedding

/-! Removing a singular head axis preserves the actual quadratic form
and pairings on its perpendicular space, with the SAME fixed tail. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedTailOrthogonality
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedTailLinear
open CFSGTwistedDFixedPolePolar CFSGTwistedDDoubleTailEmbedding
open CFSGTwistedDSingularDimensionBound CFSGTwistedDHyperbolicTripleBridge
open CFSGTwistedA2FixedField CFSGOrthogonalDIndexTailCoordinates

theorem tail_quadratic_of_negativeHead_zero (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) (hv : negativeHead n q v = 0) :
    fixedQuadraticForm n q (tailLinear n q v) = fixedQuadraticForm (n + 1) q v := by
  rw [quadratic_coordinates, hv, mul_zero, zero_add]

theorem tail_polar_of_negativeHead_zero (n : ℕ) (q : CFSG.PrimePower)
    (v w : fixedSpace (n + 1) q) (hv : negativeHead n q v = 0) (hw : negativeHead n q w = 0) :
    (fixedQuadraticForm n q).polarBilin (tailLinear n q v) (tailLinear n q w) =
      (fixedQuadraticForm (n + 1) q).polarBilin v w := by
  rw [polar_coordinates, hv, hw, mul_zero, mul_zero, zero_add, zero_add]

theorem tail_nonzero_of_not_axis (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) (hv : negativeHead n q v = 0)
    (hnot : ∀ a : fixedField q, v ≠ a • firstAxis (n + 1) q) :
    tailLinear n q v ≠ 0 := by
  intro ht
  have htK := congrArg Subtype.val ht
  have hnK := congrArg (fun a : fixedField q => a.val) hv
  have he := vector_eq_first_of_tail_zero (q.Extension 2) (n + 2) v.val htK hnK
  exact hnot (positiveHead n q v) (Subtype.ext he)

theorem tailEmbed_pairing (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace (n + 1) q) (hv : negativeHead n q v = 0) (z : fixedSpace n q) :
    (fixedQuadraticForm (n + 1) q).polarBilin v (tailEmbed n q z) =
      (fixedQuadraticForm n q).polarBilin (tailLinear n q v) z := by
  rw [polar_coordinates, hv, tailEmbed_negativeHead, tailEmbed_tail,
    mul_zero, mul_zero, zero_add, zero_add]

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedTailOrthogonality
