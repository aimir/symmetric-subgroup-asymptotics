import SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-! The rank-one symplectic base case is ordinary two-coordinate
Gaussian elimination. Both elementary matrices are literal original
C1 roots, and the form equation gives determinant one. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGTypeAElementaryMatrices
variable (K : Type) [Field K]

theorem rankOne_det_eq_one (A : Mat K 1) (hA : PreservesPairing 1 A) : A.det = 1 := by
  have h := hA (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1)
  have h' : A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inr 0) -
      A (Sum.inr 0) (Sum.inl 0) * A (Sum.inl 0) (Sum.inr 0) = 1 := by
    simpa [pairing, Matrix.mulVec_single_one, Matrix.col_apply, Fin.sum_univ_one] using h
  let e : Index 1 ≃ Fin 2 := finSumFinEquiv
  calc
    A.det = (Matrix.reindex e e A).det := (Matrix.det_reindex_self e A).symm
    _ = A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inr 0) -
        A (Sum.inl 0) (Sum.inr 0) * A (Sum.inr 0) (Sum.inl 0) := by
      rw [Matrix.det_fin_two]
      rfl
    _ = 1 := by simpa only [mul_comm] using h'

theorem rankOne_SL_toGL_mem (g : Matrix.SpecialLinearGroup (Index 1) K) :
    Matrix.SpecialLinearGroup.toGL g ∈ elementaryRootGroup K 1 := by
  let f : Matrix.SpecialLinearGroup (Index 1) K →* (Mat K 1)ˣ :=
    Matrix.SpecialLinearGroup.toGL
  let H := (elementaryRootGroup K 1).comap f
  have hH : H = ⊤ := by
    apply CFSGTypeAElementaryGeneration.eq_top_of_elementary
    intro i j hij a
    have hpoint (i : Index 1) : i = Sum.inl 0 ∨ i = Sum.inr 0 := by
      cases i with
      | inl k => exact Or.inl (congrArg Sum.inl (Subsingleton.elim k 0))
      | inr k => exact Or.inr (congrArg Sum.inr (Subsingleton.elim k 0))
    rcases hpoint i with rfl | rfl <;> rcases hpoint j with rfl | rfl
    · exact False.elim (hij rfl)
    · have he : f (elementary hij a) = rootTransvection K 1 false 0 a := by
        apply Units.ext
        change Matrix.transvection (Sum.inl 0) (Sum.inr 0) a = 1 + a • positive K 1 0
        simp [positive, Matrix.transvection, Matrix.smul_single]
      change f (elementary hij a) ∈ elementaryRootGroup K 1
      rw [he]
      exact rootTransvection_mem K 1 false 0 a
    · have he : f (elementary hij a) = rootTransvection K 1 true 0 a := by
        apply Units.ext
        change Matrix.transvection (Sum.inr 0) (Sum.inl 0) a = 1 + a • negative K 1 0
        simp [negative, positive, Matrix.transvection, Matrix.transpose_single, Matrix.smul_single]
      change f (elementary hij a) ∈ elementaryRootGroup K 1
      rw [he]
      exact rootTransvection_mem K 1 true 0 a
    · exact False.elim (hij rfl)
  exact (show g ∈ H by rw [hH]; trivial)

theorem rankOne_formPreserving_mem (u : (Mat K 1)ˣ)
    (hu : PreservesPairing 1 (u : Mat K 1)) : u ∈ elementaryRootGroup K 1 := by
  let g : Matrix.SpecialLinearGroup (Index 1) K := ⟨u.val, rankOne_det_eq_one K u.val hu⟩
  have he : Matrix.SpecialLinearGroup.toGL g = u := by apply Units.ext; rfl
  exact he ▸ rankOne_SL_toGL_mem K g

end SymmetricSubgroupAsymptotics.CFSGSymplecticStabilizerCoordinates
