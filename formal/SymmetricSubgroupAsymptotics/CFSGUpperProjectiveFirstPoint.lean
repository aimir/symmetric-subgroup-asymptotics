import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearPointAction

/-! Every literal invertible upper-triangular matrix fixes the first
projective coordinate point. No scalar-centre or group-recognition
assumption is needed. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix

namespace SymmetricSubgroupAsymptotics.CFSGUpperProjectiveFirstPoint
open CFSGProjectiveLinearPointAction CFSGProjectiveFrameCoordinates

theorem upper_fixes_first_basisPoint {K : Type*} [Field K] (n : ℕ)
    (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ)
    (hA : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K).BlockTriangular id) :
    linearEquiv A • basisPoint (F := K) (0 : Fin (n + 1)) = basisPoint 0 := by
  rw [basisPoint, Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨(A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) 0 0, ?_⟩
  change (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) 0 0 • Pi.single 0 1 =
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ Pi.single 0 1
  rw [Matrix.mulVec_single_one]
  ext i
  by_cases hi : i = 0
  · subst i
    simp [Matrix.col]
  · have hz : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i 0 = 0 :=
      hA (Fin.pos_iff_ne_zero.mpr hi)
    simp [Pi.single_apply, hi, Matrix.col, hz]

end SymmetricSubgroupAsymptotics.CFSGUpperProjectiveFirstPoint
