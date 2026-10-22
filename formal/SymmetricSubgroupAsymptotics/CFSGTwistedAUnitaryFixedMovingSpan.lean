import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMovingSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNoFixedVectors

/-! Coinvariant saturation for the actual defining-fixed natural middle
group, all ranks>=1 and every prime power, including2. Both transpose
closure and the absence of fixed vectors are proved on the literal group;
no representation-theoretic or named-group hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

def fixedMatrixHom (q : CFSG.PrimePower) (r : ℕ) :
    naturalFixed r q →* (Mat (q.Extension 2) r)ˣ :=
  (NaturalElementary (q.Extension 2) r).subtype.comp (naturalFixed r q).subtype

theorem fixedMatrix_difference_span_eq_top (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    CFSGMatrixMovingSpan.movingSpan (fixedMatrixHom q r) = ⊤ := by
  apply CFSGMatrixMovingSpan.movingSpan_eq_top
  · intro g
    refine ⟨fixedInverseTransposeHom q r g⁻¹, ?_⟩
    change (↑((g.val.val⁻¹)⁻¹) : Mat (q.Extension 2) r).transpose =
      (g.val.val : Mat (q.Extension 2) r).transpose
    rw [inv_inv]
  · intro x hx
    exact naturalFixed_no_fixed_vectors q r hr x hx

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
