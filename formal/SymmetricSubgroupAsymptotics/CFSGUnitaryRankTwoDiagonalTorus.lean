import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGTwistedA2UpperIsometricFactor

/-! Every actual diagonal defining-fixed determinant-one matrix in
dimension three is in the literal quadratic-field unit torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGTwistedA2UnipotentArrays CFSGTwistedA2DiagonalTorus

theorem rankTwo_diagonal_mem_torus (q : CFSG.PrimePower) (g : naturalFixed 2 q)
    (hdiag : ∀ i j : Fin 3, i ≠ j → (g.val.val : Mat (q.Extension 2) 2) i j = 0) :
    g ∈ (rankTwoNaturalTorus q).range := by
  have hu : (g.val.val : Mat (q.Extension 2) 2).BlockTriangular id :=
    fun _ _ h => hdiag _ _ (ne_of_gt h)
  obtain ⟨z, hz, a, b, _, he⟩ := upper_isometric_factor (q.Extension 2)
    (definingFieldAutomorphism q 2) (fun x => extension_two_pow_twice q x) g.val.val hu
    (naturalElementary_det _ _ g.val)
    (fixed_unit_isometric (q.Extension 2) 2 (definingFieldAutomorphism q 2).toRingHom
      g.val.val g.property)
  change (g.val.val : Mat (q.Extension 2) 2) =
    Matrix.diagonal (torusWeights (q.Extension 2) (definingFieldAutomorphism q 2) z) *
      upperArray (definingFieldAutomorphism q 2) a b at he
  have ha : a = 0 := by
    have hh := congrArg (fun M : Mat (q.Extension 2) 2 => M 0 1) he
    dsimp only at hh
    rw [hdiag 0 1 (by decide), Matrix.diagonal_mul] at hh
    have hh' : z * a = 0 := by simpa [torusWeights, upperArray] using hh.symm
    exact (mul_eq_zero.mp hh').resolve_left hz
  have hb : b = 0 := by
    have hh := congrArg (fun M : Mat (q.Extension 2) 2 => M 0 2) he
    dsimp only at hh
    rw [hdiag 0 2 (by decide), Matrix.diagonal_mul] at hh
    have hh' : z * b = 0 := by simpa [torusWeights, upperArray] using hh.symm
    exact (mul_eq_zero.mp hh').resolve_left hz
  rw [ha, hb, upperArray_zero, mul_one] at he
  refine ⟨Units.mk0 z hz, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  exact (torusNatural_val _ _ z hz).trans he.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
