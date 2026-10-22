import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialElements
import SymmetricSubgroupAsymptotics.CFSGDiagonalUnitRootAction

/-! Exact diagonal action on the initial B roots. The quadratic short
root uses weight l on its linear term and l² on its quadratic term;
the proof is on actual units and never discards the middle coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationDiagonalAction
open Matrix CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationInitialElements
variable (K : Type) [Field K]

private theorem quadratic_line_conjugation {I : Type*} [Fintype I] [DecidableEq I]
    (T U V : (Matrix I I K)ˣ) (d : I → K) (X Y : Matrix I I K) (l a : K)
    (hT : (T : Matrix I I K) = Matrix.diagonal d)
    (hU : (U : Matrix I I K) = 1 + a • X + a ^ 2 • Y)
    (hV : (V : Matrix I I K) = 1 + (l * a) • X + (l * a) ^ 2 • Y)
    (hX : ∀ i j, X i j ≠ 0 → d i = l * d j)
    (hY : ∀ i j, Y i j ≠ 0 → d i = l ^ 2 * d j) : T * U * T⁻¹ = V := by
  have hDX := CFSGDiagonalUnitRootAction.diagonal_intertwines d X l hX
  have hDY := CFSGDiagonalUnitRootAction.diagonal_intertwines d Y (l ^ 2) hY
  have hm : T * U = V * T := by
    apply Units.ext
    change (T : Matrix I I K) * (U : Matrix I I K) =
      (V : Matrix I I K) * (T : Matrix I I K)
    rw [hT, hU, hV]
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm,
      hDX, hDY, smul_mul_assoc, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hh := congrArg (fun Z : (Matrix I I K)ˣ => Z * T⁻¹) hm
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh

theorem alpha_diagonal_conjugation (s : ℕ) (T : (Mat K (s + 3))ˣ)
    (d : Index (s + 3) → K) (hT : (T : Mat K (s + 3)) = Matrix.diagonal d) (l a : K)
    (hp : d (pos (s + 3) (lastIndex s)) = l * d (pos (s + 3) (penIndex s)))
    (hn : d (CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s)) =
      l * d (CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s))) :
    T * alphaUnit K s a * T⁻¹ = alphaUnit K s (l * a) := by
  apply CFSGDiagonalUnitRootAction.root_line_conjugation T (alphaUnit K s a)
    (alphaUnit K s (l * a)) d (alphaArray K s) l a hT
    (alphaUnit_val K s a) (alphaUnit_val K s (l * a))
  intro i j hX
  by_cases hpos : pos (s + 3) (lastIndex s) = i ∧ pos (s + 3) (penIndex s) = j
  · rcases hpos with ⟨rfl, rfl⟩
    exact hp
  · by_cases hneg : CFSGOrthogonalBSerreMatrices.neg (s + 3) (penIndex s) = i ∧
        CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s) = j
    · rcases hneg with ⟨rfl, rfl⟩
      exact hn
    · have hz : alphaArray K s i j = 0 := by
        simp only [alphaArray, Matrix.sub_apply, Matrix.single_apply,
          hpos, hneg, if_false, sub_self]
      exact (hX hz).elim

theorem beta_diagonal_conjugation (s : ℕ) (T : (Mat K (s + 3))ˣ)
    (d : Index (s + 3) → K) (hT : (T : Mat K (s + 3)) = Matrix.diagonal d) (l a : K)
    (hp : d (pos (s + 3) (lastIndex s)) = l * d (middle (s + 3)))
    (hn : d (middle (s + 3)) = l * d (CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s))) :
    T * betaUnit K s a * T⁻¹ = betaUnit K s (l * a) := by
  apply quadratic_line_conjugation K T (betaUnit K s a) (betaUnit K s (l * a)) d
    (shortArray K (s + 3) (Sum.inl (lastIndex s)))
    (shortSecond K (s + 3) (Sum.inl (lastIndex s))) l a hT (by rfl) (by rfl)
  · intro i j hX
    by_cases hpos : pos (s + 3) (lastIndex s) = i ∧ middle (s + 3) = j
    · rcases hpos with ⟨rfl, rfl⟩
      exact hp
    · by_cases hneg : middle (s + 3) = i ∧
          CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s) = j
      · rcases hneg with ⟨rfl, rfl⟩
        exact hn
      · have hz : shortArray K (s + 3) (Sum.inl (lastIndex s)) i j = 0 := by
          simp only [shortArray, paired, Sum.swap, Sum.elim_inl, Matrix.sub_apply,
            Matrix.single_apply, hpos, hneg, if_false, sub_self]
        exact (hX hz).elim
  · intro i j hY
    by_cases hpos : pos (s + 3) (lastIndex s) = i ∧
        CFSGOrthogonalBSerreMatrices.neg (s + 3) (lastIndex s) = j
    · rcases hpos with ⟨rfl, rfl⟩
      rw [hp, hn, pow_two, mul_assoc]
    · have hz : shortSecond K (s + 3) (Sum.inl (lastIndex s)) i j = 0 := by
        simp only [shortSecond, paired, Sum.swap, Sum.elim_inl, Matrix.single_apply, hpos, if_false]
      exact (hY hz).elim

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationDiagonalAction
