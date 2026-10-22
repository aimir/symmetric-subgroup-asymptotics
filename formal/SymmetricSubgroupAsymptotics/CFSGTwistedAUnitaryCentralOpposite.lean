import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralRoot
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositePivot
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction

/-! The genuine opposite of the central upper root has exactly the
lower extreme coefficient -t^-1. Its upper parameter is the proved valid
-eps*t^-1, and the signed-reversal row ratio supplies the exact sign.
This retains the SAME original defining-fixed subgroup and all fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical

def centralOppositeFixed (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) : naturalFixed (s + 2) q :=
  reversalFixed q (s + 2) *
    centralFixed q s (-parity q s * t⁻¹) (central_inverse_parameter_condition q s t ht) *
      (reversalFixed q (s + 2))⁻¹

theorem centralOppositeFixed_mem (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) :
    (centralOppositeFixed q s t ht).val ∈ oppositeNaturalUnipotent q (s + 2) := by
  exact ⟨(radicalElement q s 0 (-parity q s * t⁻¹)
    (central_inverse_parameter_condition q s t ht)).val,
    (radicalElement q s 0 (-parity q s * t⁻¹)
      (central_inverse_parameter_condition q s t ht)).property, rfl⟩

theorem centralOpposite_matrix (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : Condition q s 0 t) :
    ((centralOppositeFixed q s t ht).val.val : Mat (q.Extension 2) (s + 2)) =
      1 + Matrix.single (Fin.last (s + 2)) (0 : Fin (s + 3)) (-t⁻¹) := by
  let J := signedReversalUnit (q.Extension 2) (s + 2)
  have h0 : (0 : Fin (s + 3)).rev = Fin.last (s + 2) := by
    apply Fin.ext
    simp [Fin.rev]
  have hl : (Fin.last (s + 2)).rev = (0 : Fin (s + 3)) := by
    apply Fin.ext
    simp [Fin.rev]
  have hw0 : signWeight (q.Extension 2) (s + 2) 0 = 1 := by simp [signWeight]
  have hwl : signWeight (q.Extension 2) (s + 2) (Fin.last (s + 2)) = parity q s := by
    change (-1 : q.Extension 2) ^ (s + 2) = (-1 : q.Extension 2) ^ s
    rw [pow_add]
    simp
  have hp : parity q s * parity q s = 1 := by
    change ((-1 : q.Extension 2) ^ s) * ((-1 : q.Extension 2) ^ s) = 1
    rw [← mul_pow]
    simp
  have hc := CFSGOrthogonalDGenerationMonomialAction.conjugation_single J Fin.revPerm
    (signWeight (q.Extension 2) (s + 2)) (signedReversalUnit_monomial (q.Extension 2) (s + 2))
    0 (Fin.last (s + 2)) (-parity q s * t⁻¹)
    (signWeight_ne_zero (q.Extension 2) (s + 2) _)
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, h0, hl, hw0, hwl, div_one] at hc
  have hcoef : parity q s * (-parity q s * t⁻¹) = -t⁻¹ := by
    calc
      _ = -(parity q s * parity q s) * t⁻¹ := by ring
      _ = _ := by rw [hp]; ring
  rw [hcoef] at hc
  change (J : Mat (q.Extension 2) (s + 2)) *
    ((radicalElement q s 0 (-parity q s * t⁻¹)
      (central_inverse_parameter_condition q s t ht)).val.val : Mat (q.Extension 2) (s + 2)) *
        (↑(J⁻¹) : Mat (q.Extension 2) (s + 2)) = _
  rw [radicalCentral_matrix]
  simp only [mul_add, add_mul, mul_one, Units.mul_inv]
  rw [hc]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
