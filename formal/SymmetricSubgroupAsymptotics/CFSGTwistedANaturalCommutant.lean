import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalRealization

/-! The common commutant of the literal adjacent positive and negative
A-root matrices is scalar. This all-characteristic statement needs neither
a full-SL identification nor a source-simplicity assumption. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable (K : Type) [Field K] (r : ℕ)

theorem natural_commutant_scalar (hr : 1 ≤ r) (M : Mat K r)
    (hroot : ∀ neg i, M * rootMatrix K r neg i = rootMatrix K r neg i * M) :
    ∃ c : K, M = c • (1 : Mat K r) := by
  have hpos (i : Fin r) : M * Matrix.single i.castSucc i.succ (1 : K) =
      Matrix.single i.castSucc i.succ 1 * M := by
    simpa only [rootMatrix, Bool.false_eq_true, if_false, positive] using hroot false i
  have hneg (i : Fin r) : M * Matrix.single i.succ i.castSucc (1 : K) =
      Matrix.single i.succ i.castSucc 1 * M := by
    simpa only [rootMatrix, if_true, negative, positive, Matrix.transpose_single] using hroot true i
  have hdiag (i : Fin r) : M i.castSucc i.castSucc = M i.succ i.succ := by
    have h := congrArg (fun A : Mat K r => A i.castSucc i.succ) (hpos i)
    dsimp only at h
    simpa only [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, mul_one, one_mul] using h
  have hoff : ∀ a b : Fin (r + 1), a ≠ b → M a b = 0 := by
    intro a b hab
    induction b using Fin.cases with
    | zero =>
      let i : Fin r := ⟨0, by omega⟩
      have hi0 : i.castSucc = (0 : Fin (r + 1)) := by apply Fin.ext; simp [i]
      have hai : a ≠ i.castSucc := by rwa [hi0]
      have h := congrArg (fun A : Mat K r => A a i.succ) (hpos i)
      dsimp only at h
      have hz : (Matrix.single i.castSucc i.succ (1 : K) * M) a i.succ = 0 :=
        Matrix.single_mul_apply_of_ne (1 : K) i.castSucc i.succ a i.succ hai M
      rw [Matrix.mul_single_apply_same, hz] at h
      simpa only [hi0, mul_one] using h
    | succ i =>
      have h := congrArg (fun A : Mat K r => A a i.castSucc) (hneg i)
      dsimp only at h
      have hz : (Matrix.single i.succ i.castSucc (1 : K) * M) a i.castSucc = 0 :=
        Matrix.single_mul_apply_of_ne (1 : K) i.succ i.castSucc a i.castSucc hab M
      rw [Matrix.mul_single_apply_same, hz] at h
      simpa only [mul_one] using h
  have hconstant : ∀ i : Fin (r + 1), M i i = M 0 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i hi => exact (hdiag i).symm.trans hi
  refine ⟨M 0 0, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst b
    simpa only [Matrix.smul_apply, Matrix.one_apply, if_pos rfl, if_true,
      smul_eq_mul, mul_one] using hconstant a
  · simp only [hoff a b hab, Matrix.smul_apply, Matrix.one_apply, if_neg hab,
      smul_eq_mul, mul_zero]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
