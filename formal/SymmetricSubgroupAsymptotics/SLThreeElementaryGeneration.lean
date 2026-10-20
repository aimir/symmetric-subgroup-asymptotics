import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Elementary generation and perfectness of SL(3)

A direct elementary-matrix proof over any field.  Gaussian elimination is
mathlib's checked diagonal/transvection induction.  The diagonal factors and
the commutator identity are proved here by matrix multiplication.
-/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.SLThreeElementary
variable {F : Type*} [Field F]
abbrev SL := Matrix.SpecialLinearGroup (Fin 3) F

/-- Elementary determinant-one matrix. -/
def elementary {i j : Fin 3} (hij : i ≠ j) (a : F) : SL (F := F) :=
  ⟨Matrix.transvection i j a, Matrix.det_transvection_of_ne i j hij a⟩

@[simp] theorem elementary_coe {i j : Fin 3} (hij : i ≠ j) (a : F) :
    (elementary hij a).1 = Matrix.transvection i j a := rfl

@[simp] theorem elementary_inv {i j : Fin 3} (hij : i ≠ j) (a : F) :
    (elementary hij a)⁻¹ = elementary hij (-a) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.transvection_mul_transvection_same, hij]

private theorem diagonalPair01 (a : F) (ha : a ≠ 0) :
    Matrix.transvection (0 : Fin 3) 1 (a - 1) * Matrix.transvection 1 0 1 *
      Matrix.transvection 0 1 (a⁻¹ - 1) * Matrix.transvection 1 0 (-a) =
        Matrix.diagonal ![a, a⁻¹, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.one_apply, Matrix.diagonal] <;> field_simp [ha] <;> (ring_nf; all_goals simp)

private theorem diagonalPair12 (a : F) (ha : a ≠ 0) :
    Matrix.transvection (1 : Fin 3) 2 (a - 1) * Matrix.transvection 2 1 1 *
      Matrix.transvection 1 2 (a⁻¹ - 1) * Matrix.transvection 2 1 (-a) =
        Matrix.diagonal ![1, a, a⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.one_apply, Matrix.diagonal] <;> field_simp [ha] <;> (ring_nf; all_goals simp)

/-- Any subgroup containing the elementary matrices is all of SL(3). -/
theorem eq_top_of_elementary (H : Subgroup (SL (F := F)))
    (hH : ∀ (i j : Fin 3) (hij : i ≠ j) (a : F), elementary hij a ∈ H) : H = ⊤ := by
  have allMatrices : ∀ M : Matrix (Fin 3) (Fin 3) F, M.det = 1 →
      ∃ A : SL (F := F), A ∈ H ∧ A.1 = M := by
    intro M hM
    apply Matrix.diagonal_transvection_induction
      (fun T => ∃ A : SL (F := F), A ∈ H ∧ A.1 = T) M
    · intro D hD
      have hprod : D 0 * D 1 * D 2 = 1 := by
        simpa [Matrix.det_diagonal, Fin.prod_univ_succ, mul_assoc] using hD.trans hM
      have h01 : D 0 * D 1 ≠ 0 := by
        intro h; rw [h, zero_mul] at hprod; exact zero_ne_one hprod
      have h0 : D 0 ≠ 0 := (mul_ne_zero_iff.mp h01).1
      let A : SL (F := F) :=
        elementary (by decide : (0 : Fin 3) ≠ 1) (D 0 - 1) *
        elementary (by decide : (1 : Fin 3) ≠ 0) 1 *
        elementary (by decide : (0 : Fin 3) ≠ 1) ((D 0)⁻¹ - 1) *
        elementary (by decide : (1 : Fin 3) ≠ 0) (-D 0)
      let B : SL (F := F) :=
        elementary (by decide : (1 : Fin 3) ≠ 2) (D 0 * D 1 - 1) *
        elementary (by decide : (2 : Fin 3) ≠ 1) 1 *
        elementary (by decide : (1 : Fin 3) ≠ 2) ((D 0 * D 1)⁻¹ - 1) *
        elementary (by decide : (2 : Fin 3) ≠ 1) (-(D 0 * D 1))
      refine ⟨A * B, H.mul_mem ?_ ?_, ?_⟩
      · exact H.mul_mem (H.mul_mem (H.mul_mem (hH _ _ _ _) (hH _ _ _ _))
          (hH _ _ _ _)) (hH _ _ _ _)
      · exact H.mul_mem (H.mul_mem (H.mul_mem (hH _ _ _ _) (hH _ _ _ _))
          (hH _ _ _ _)) (hH _ _ _ _)
      · change _ * _ = Matrix.diagonal D
        change (Matrix.transvection 0 1 (D 0 - 1) * Matrix.transvection 1 0 1 *
          Matrix.transvection 0 1 ((D 0)⁻¹ - 1) * Matrix.transvection 1 0 (-D 0)) *
          (Matrix.transvection 1 2 (D 0 * D 1 - 1) * Matrix.transvection 2 1 1 *
          Matrix.transvection 1 2 ((D 0 * D 1)⁻¹ - 1) *
          Matrix.transvection 2 1 (-(D 0 * D 1))) = Matrix.diagonal D
        rw [diagonalPair01 _ h0, diagonalPair12 _ h01, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i
        · simp
        · simp [h0]
        · simpa using (inv_eq_of_mul_eq_one_right hprod)
    · rintro ⟨i, j, hij, a⟩
      exact ⟨elementary hij a, hH i j hij a, rfl⟩
    · rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
      exact ⟨A * B, H.mul_mem hA hB, rfl⟩
  apply top_unique
  intro A _
  obtain ⟨B, hB, hBA⟩ := allMatrices A.1 A.2
  exact (Subtype.ext hBA : B = A) ▸ hB

/-- Each elementary matrix is a commutator, using the third coordinate. -/
theorem elementary_commutator (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hkj : k ≠ j) (a : F) :
    ⁅elementary hik a, elementary hkj (1 : F)⁆ = elementary hij a := by
  rw [commutatorElement_def, elementary_inv, elementary_inv]
  apply Subtype.ext
  change (Matrix.transvection i k a * Matrix.transvection k j 1 *
    Matrix.transvection i k (-a) * Matrix.transvection k j (-1)) = Matrix.transvection i j a
  fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
  all_goals
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

/-- SL(3) is perfect over every field, including F₂ and F₃. -/
theorem commutator_eq_top : commutator (SL (F := F)) = ⊤ := by
  apply eq_top_of_elementary
  intro i j hij a
  obtain ⟨k, hik, hkj⟩ : ∃ k : Fin 3, i ≠ k ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> first | contradiction | decide
  rw [← elementary_commutator i j k hij hik hkj a]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end SymmetricSubgroupAsymptotics.SLThreeElementary
