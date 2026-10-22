import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NoncommRing

/-! Literal unit-matrix displacements determine the original unit and
satisfy the exact product identity, including the actual mixed term. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixDisplacement
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def displacement (g : (Matrix I I K)ˣ) : (I → K) →ₗ[K] (I → K) :=
  Matrix.mulVecLin ((g : Matrix I I K) - 1)

theorem displacement_injective : Function.Injective (displacement (K := K) (I := I)) := by
  intro g h he
  apply Units.ext
  have hm : ((g : Matrix I I K) - 1) = ((h : Matrix I I K) - 1) := by
    ext i j
    have hx := congrFun (LinearMap.congr_fun he (Pi.single j 1)) i
    simpa only [displacement, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hx
  have h := congrArg (fun M : Matrix I I K => M + 1) hm
  simpa only [sub_add_cancel] using h

theorem displacement_mul (g h : (Matrix I I K)ˣ) :
    displacement (g * h) = displacement g + displacement h +
      (displacement g).comp (displacement h) := by
  have hm : ((g * h : (Matrix I I K)ˣ) : Matrix I I K) - 1 =
      ((g : Matrix I I K) - 1) + ((h : Matrix I I K) - 1) +
        ((g : Matrix I I K) - 1) * ((h : Matrix I I K) - 1) := by
    change (g : Matrix I I K) * (h : Matrix I I K) - 1 = _
    noncomm_ring
  change Matrix.mulVecLin _ = _
  rw [hm, Matrix.mulVecLin_add, Matrix.mulVecLin_add, Matrix.mulVecLin_mul]
  rfl

end SymmetricSubgroupAsymptotics.CFSGMatrixDisplacement
