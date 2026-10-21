import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootBasisAction
import SymmetricSubgroupAsymptotics.CFSGMatrixCyclicCentralizer

/-! The actual natural type-B root commutant is scalar away from
characteristic two. Short-root coefficients are cancelled explicitly. -/
set_option autoImplicit false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSGMatrixCyclicCentralizer
variable {K : Type*} [Field K]

theorem simple_root_centralizer (r : ℕ) (h2 : (2 : K) ≠ 0) (A : Mat K (r + 1))
    (hE : ∀ i, A * positive K (r + 1) i = positive K (r + 1) i * A)
    (hF : ∀ i, A * negative K (r + 1) i = negative K (r + 1) i * A) :
    ∃ c : K, A = c • (1 : Mat K (r + 1)) := by
  let j := Fin.last r
  let c := A (pos (r + 1) j) (pos (r + 1) j)
  have hE2 : A * (positive K (r + 1) j * positive K (r + 1) j) =
      (positive K (r + 1) j * positive K (r + 1) j) * A := by
    rw [← mul_assoc, hE, mul_assoc, hE, ← mul_assoc]
  have hF2 : A * (negative K (r + 1) j * negative K (r + 1) j) =
      (negative K (r + 1) j * negative K (r + 1) j) * A := by
    rw [← mul_assoc, hF, mul_assoc, hF, ← mul_assoc]
  have hprod : A * ((positive K (r + 1) j * positive K (r + 1) j) *
        (negative K (r + 1) j * negative K (r + 1) j)) =
      ((positive K (r + 1) j * positive K (r + 1) j) *
        (negative K (r + 1) j * negative K (r + 1) j)) * A := by
    rw [← mul_assoc, hE2, mul_assoc, hF2, ← mul_assoc]
  rw [terminal_square_product] at hprod
  have h4 : (4 : K) ≠ 0 := by
    have h := mul_ne_zero h2 h2
    norm_num at h ⊢
    exact h
  have hproj : A * Matrix.single (pos (r + 1) j) (pos (r + 1) j) 1 =
      Matrix.single (pos (r + 1) j) (pos (r + 1) j) 1 * A := by
    have hh : (4 : K) • (A * Matrix.single (pos (r + 1) j) (pos (r + 1) j) 1) =
        (4 : K) • (Matrix.single (pos (r + 1) j) (pos (r + 1) j) 1 * A) := by
      rw [← mul_smul_comm, ← smul_mul_assoc, Matrix.smul_single, smul_eq_mul, mul_one]
      exact hprod
    ext i k
    have he := congrArg (fun M : Mat K (r + 1) => M i k) hh
    exact mul_left_cancel₀ h4 he
  have hpos : A *ᵥ Pi.single (pos (r + 1) j) 1 =
      c • Pi.single (pos (r + 1) j) 1 :=
    eigenvector_of_commutes_projection A (pos (r + 1) j) hproj
  have hmiddle : A *ᵥ Pi.single (middle (r + 1)) 1 =
      c • Pi.single (middle (r + 1)) 1 := by
    have h := eigenvector_of_commutes A (negative K (r + 1) j) (hF j)
      (Pi.single (pos (r + 1) j) 1) c hpos
    rw [negative_last_positive_basis] at h
    simp only [Matrix.mulVec_smul, smul_comm c (2 : K)] at h
    funext i
    have he := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at he
    exact mul_left_cancel₀ h2 he
  have hneg : A *ᵥ Pi.single (neg (r + 1) j) 1 =
      c • Pi.single (neg (r + 1) j) 1 := by
    have h := eigenvector_of_commutes A (negative K (r + 1) j) (hF j)
      (Pi.single (middle (r + 1)) 1) c hmiddle
    rw [negative_last_middle_basis] at h
    apply neg_injective
    simpa only [Matrix.mulVec_neg, smul_neg] using h
  have hall : ∀ i : Fin (r + 1),
      (A *ᵥ Pi.single (pos (r + 1) i) 1 = c • Pi.single (pos (r + 1) i) 1) ∧
      (A *ᵥ Pi.single (neg (r + 1) i) 1 = c • Pi.single (neg (r + 1) i) 1) := by
    intro i
    induction i using Fin.reverseInduction with
    | last => exact ⟨hpos, hneg⟩
    | cast i ih =>
      have hp := eigenvector_of_commutes A (positive K (r + 1) i.castSucc)
        (hE i.castSucc) (Pi.single (pos (r + 1) i.succ) 1) c ih.1
      rw [positive_castSucc_basis] at hp
      have hn := eigenvector_of_commutes A (negative K (r + 1) i.castSucc)
        (hF i.castSucc) (Pi.single (neg (r + 1) i.succ) 1) c ih.2
      rw [negative_castSucc_basis] at hn
      exact ⟨hp, neg_injective (by simpa only [Matrix.mulVec_neg, smul_neg] using hn)⟩
  refine ⟨c, Matrix.ext_of_mulVec_single ?_⟩
  intro y
  have hy : A *ᵥ Pi.single y 1 = c • Pi.single y 1 := by
    cases y with
    | inl i =>
      cases i with
      | inl i => exact (hall i).1
      | inr i => exact (hall i).2
    | inr i => cases i; exact hmiddle
  simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using hy

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
