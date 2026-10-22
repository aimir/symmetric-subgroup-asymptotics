import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexForm
import SymmetricSubgroupAsymptotics.CFSGThreeDimensionalOrthogonalStabilizer
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneTorus
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! The rank-one determinant-one first-vector stabilizer lies in the
SAME original elementary group. Reindexing has exactly three coordinates;
the returned element is a literal original short-root word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneStabilizer
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationShortMembership
variable (K : Type) [Field K]

def coordinateEquiv : Fin 3 ≃ Index 1 where
  toFun i := ![pos 1 0, neg 1 0, middle 1] i
  invFun x := match x with
    | .inl (.inl _) => 0
    | .inl (.inr _) => 1
    | .inr _ => 2
  left_inv i := by fin_cases i <;> rfl
  right_inv x := by
    rcases x with (i | i) | i
    · fin_cases i
      rfl
    · fin_cases i
      rfl
    · cases i
      rfl

theorem gram_reindex : (gram K 1).submatrix coordinateEquiv coordinateEquiv =
    CFSGThreeDimensionalOrthogonalStabilizer.gram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateEquiv, gram, CFSGThreeDimensionalOrthogonalStabilizer.gram, pos, neg, middle]

theorem short_reindex (t : K) :
    (shortUnit K 1 (Sum.inl 0) t : Mat K 1).submatrix coordinateEquiv coordinateEquiv =
      !![1, -(t ^ 2), t; 0, 1, 0; 0, -2 * t, 1] := by
  rw [shortUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateEquiv, shortArray, shortSecond, paired, pos, neg, middle,
      Matrix.submatrix_apply] <;> ring

theorem first_vector_stabilizer_elementary (h2 : (2 : K) ≠ 0) (g : Mat K 1)
    (hf : g.transpose * gram K 1 * g = gram K 1) (hd : g.det = 1)
    (hu : g *ᵥ Pi.single (pos 1 0) 1 = Pi.single (pos 1 0) 1) :
    ∃ s : elementaryRootGroup K 1, (s.val : Mat K 1) = g := by
  let A := g.submatrix coordinateEquiv coordinateEquiv
  have hA : A.transpose * CFSGThreeDimensionalOrthogonalStabilizer.gram * A =
      CFSGThreeDimensionalOrthogonalStabilizer.gram := by
    calc
      _ = g.transpose.submatrix coordinateEquiv coordinateEquiv *
          (gram K 1).submatrix coordinateEquiv coordinateEquiv *
          g.submatrix coordinateEquiv coordinateEquiv := by rw [gram_reindex]; rfl
      _ = (g.transpose * gram K 1 * g).submatrix coordinateEquiv coordinateEquiv := by
        rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
      _ = _ := (congrArg (fun M : Mat K 1 => M.submatrix coordinateEquiv coordinateEquiv) hf).trans
        (gram_reindex K)
  have hdet : A.det = 1 := (Matrix.det_submatrix_equiv_self coordinateEquiv g).trans hd
  rw [Matrix.mulVec_single_one] at hu
  have hcol (i : Index 1) := congrFun hu i
  have h00 : A 0 0 = 1 := by
    simpa [A, coordinateEquiv, pos, neg, middle] using hcol (pos 1 0)
  have h10 : A 1 0 = 0 := by
    simpa [A, coordinateEquiv, pos, neg, middle, Pi.single_apply] using hcol (neg 1 0)
  have h20 : A 2 0 = 0 := by
    simpa [A, coordinateEquiv, pos, neg, middle, Pi.single_apply] using hcol (middle 1)
  obtain ⟨t, ht⟩ := CFSGThreeDimensionalOrthogonalStabilizer.first_column_stabilizer
    h2 A hA hdet h00 h10 h20
  let s : elementaryRootGroup K 1 := ⟨shortUnit K 1 (Sum.inl 0) t, shortUnit_mem K 0 (Sum.inl 0) t⟩
  refine ⟨s, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := coordinateEquiv.surjective i
  obtain ⟨j, rfl⟩ := coordinateEquiv.surjective j
  exact (congrFun (congrFun (short_reindex K t) i) j).trans
    (congrFun (congrFun ht i) j).symm

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIsometryIndexRankOneStabilizer
