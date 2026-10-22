import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Concrete symmetric matrices annihilated by every positive GL
root commutator have only their first diagonal and first symmetric
pair free. The pair coefficient is killed by two. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymmetricUpperCentralizer
variable {K : Type} [Field K] {n : ℕ}

private theorem row_zero (B : Matrix (Fin n) (Fin n) K) (i j k : Fin n)
    (hk : k ≠ i)
    (he : Matrix.single i j 1 * B + B * Matrix.single j i 1 = 0) : B j k = 0 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i k) he
  dsimp only at h
  simpa only [Matrix.add_apply, Matrix.single_mul_apply_same, one_mul,
    Matrix.mul_single_apply_of_ne (1 : K) j i i k hk B, add_zero, Matrix.zero_apply] using h

theorem symmetric_upper_centralizer (r : ℕ) (hr : 0 < r)
    (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hB : B.IsSymm)
    (hcomm : ∀ i j : Fin (r + 1), i < j →
      Matrix.single i j 1 * B + B * Matrix.single j i 1 = 0) :
    let k : Fin (r + 1) := ⟨1, Nat.succ_lt_succ hr⟩
    (2 : K) * B 0 k = 0 ∧
      B = Matrix.single 0 0 (B 0 0) + Matrix.single 0 k (B 0 k) + Matrix.single k 0 (B 0 k) := by
  let k : Fin (r + 1) := ⟨1, Nat.succ_lt_succ hr⟩
  change (2 : K) * B 0 k = 0 ∧
    B = Matrix.single 0 0 (B 0 0) + Matrix.single 0 k (B 0 k) + Matrix.single k 0 (B 0 k)
  have hk0 : k ≠ 0 := by intro h; have hv := congrArg Fin.val h; change 1 = 0 at hv; omega
  have h0k : (0 : Fin (r + 1)) < k := by change 0 < 1; omega
  have hrow (j a : Fin (r + 1)) (hj : 0 < j) (ha : a ≠ 0) : B j a = 0 :=
    row_zero B 0 j a ha (hcomm 0 j hj)
  have hother (i j : Fin (r + 1)) (hi0 : i ≠ 0) (hik : i ≠ k) : B i j = 0 := by
    by_cases hj : j = 0
    · subst j
      have hki : k < i := by
        have hi := i.isLt
        have hz : i.val ≠ 0 := by intro h; exact hi0 (Fin.ext h)
        have ho : i.val ≠ 1 := by intro h; exact hik (Fin.ext h)
        change 1 < i.val
        omega
      exact row_zero B k i 0 (Ne.symm hk0) (hcomm k i hki)
    · have hi : 0 < i := by
        change 0 < i.val
        have hz : i.val ≠ 0 := by intro h; exact hi0 (Fin.ext h)
        omega
      exact hrow i j hi hj
  have hp := congrArg (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) K => M 0 0) (hcomm 0 k h0k)
  dsimp only at hp
  simp only [Matrix.add_apply, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same,
    one_mul, mul_one, Matrix.zero_apply] at hp
  have hb2 : (2 : K) * B 0 k = 0 := by
    rw [hB.apply 0 k] at hp
    calc
      (2 : K) * B 0 k = B 0 k + B 0 k := by ring
      _ = 0 := hp
  refine ⟨hb2, ?_⟩
  ext i j
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · subst j
      simp [Matrix.single_apply, hk0, Ne.symm hk0]
    · by_cases hjk : j = k
      · subst j
        simp [Matrix.single_apply, hk0, Ne.symm hk0]
      · have hz : B 0 j = 0 := (hB.apply 0 j).symm.trans (hother j 0 hj0 hjk)
        simp [Matrix.single_apply, hj0, Ne.symm hj0, hjk, Ne.symm hjk, hz]
  · by_cases hik : i = k
    · subst i
      by_cases hj0 : j = 0
      · subst j
        simp [Matrix.single_apply, hk0, Ne.symm hk0, hB.apply 0 k]
      · have hz : B k j = 0 := hrow k j h0k hj0
        simp [Matrix.single_apply, hk0, Ne.symm hk0, hj0, Ne.symm hj0, hz]
    · have hz := hother i j hi0 hik
      simp [Matrix.single_apply, hi0, Ne.symm hi0, hik, Ne.symm hik, hz]

end SymmetricSubgroupAsymptotics.CFSGSymmetricUpperCentralizer
