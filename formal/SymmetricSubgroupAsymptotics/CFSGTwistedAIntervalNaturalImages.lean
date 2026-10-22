import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalFiniteSpan
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalRealization

/-! The actual rational natural image of every original interval vector.
The coefficient of a negative right-nested interval is an explicit unit
sign. All matrix calculations are symbolic in the rank. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSG.Models.Chevalley CFSGSerreDividedPowers CFSGTwistedANaturalMatrices
open CFSGTwistedAIntervalBrackets

theorem interval_one (r : ℕ) (neg : Bool) (start : ℕ) :
    interval r neg start 1 = simple r neg start :=
  chainBracket_one (simple r neg) start

theorem interval_step (r : ℕ) (neg : Bool) (start n : ℕ) :
    interval r neg start (n + 2) =
      ⁅simple r neg start, interval r neg (start + 1) (n + 1)⁆ :=
  chainBracket_step (simple r neg) start n

theorem matrixUnit_chain_lie {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (a b c : J) (hac : a ≠ c) (t : R) :
    ⁅(Matrix.single a b (1 : R) : Matrix J J R), Matrix.single b c t⁆ =
      Matrix.single a c t := by
  rw [Ring.lie_def, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne t b c a hac.symm 1, one_mul, sub_zero]

theorem matrixUnit_reverse_lie {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (a b c : J) (hac : a ≠ c) (t : R) :
    ⁅(Matrix.single b a (1 : R) : Matrix J J R), Matrix.single c b t⁆ =
      -Matrix.single c a t := by
  rw [Ring.lie_def, Matrix.single_mul_single_of_ne 1 b a c hac t,
    Matrix.single_mul_single_same, mul_one, zero_sub]

theorem matrixUnit_neg {R J : Type*} [CommRing R] [DecidableEq J]
    (a b : J) (t : R) :
    (Matrix.single a b (-t) : Matrix J J R) = -Matrix.single a b t := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem natural_simple_positive (r k : ℕ) (hk : k < r) :
    rationalNatural r (simple r false k) = positive ℚ r ⟨k, hk⟩ := by
  simpa only [simple, dif_pos hk, rootVector, Bool.false_eq_true, if_false] using
    rationalNatural_E r ⟨k, hk⟩

theorem natural_simple_negative (r k : ℕ) (hk : k < r) :
    rationalNatural r (simple r true k) = negative ℚ r ⟨k, hk⟩ := by
  simpa only [simple, dif_pos hk, rootVector, if_true] using
    rationalNatural_F r ⟨k, hk⟩

theorem natural_interval_positive (r start n : ℕ) (hn : 0 < n) (hend : start + n ≤ r) :
    rationalNatural r (interval r false start n) =
      Matrix.single (⟨start, by omega⟩ : Fin (r + 1)) ⟨start + n, by omega⟩ 1 := by
  induction n using Nat.twoStepInduction generalizing start with
  | zero => omega
  | one =>
    rw [interval_one]
    rw [natural_simple_positive r start (by omega)]
    rfl
  | more n _ ih =>
    rw [interval_step]
    rw [(rationalNatural r).map_lie, natural_simple_positive r start (by omega),
      ih (start + 1) (by omega) (by omega)]
    have he : start + 1 + (n + 1) = start + (n + 2) := by omega
    simp only [he]
    have hne : (⟨start, by omega⟩ : Fin (r + 1)) ≠
        (⟨start + (n + 2), by omega⟩ : Fin (r + 1)) := by
      intro hh
      have hv := congrArg (fun i : Fin (r + 1) => i.val) hh
      dsimp only at hv
      omega
    simpa only [positive] using
      matrixUnit_chain_lie (⟨start, by omega⟩ : Fin (r + 1))
        ⟨start + 1, by omega⟩ ⟨start + (n + 2), by omega⟩ hne (1 : ℚ)

theorem natural_interval_negative (r start n : ℕ) (hn : 0 < n) (hend : start + n ≤ r) :
    rationalNatural r (interval r true start n) =
      Matrix.single (⟨start + n, by omega⟩ : Fin (r + 1)) ⟨start, by omega⟩
        ((-1 : ℚ) ^ (n - 1)) := by
  induction n using Nat.twoStepInduction generalizing start with
  | zero => omega
  | one =>
    rw [interval_one]
    rw [natural_simple_negative r start (by omega)]
    simp only [negative, positive, Matrix.transpose_single, Nat.sub_self, pow_zero]
    rfl
  | more n _ ih =>
    rw [interval_step]
    rw [(rationalNatural r).map_lie, natural_simple_negative r start (by omega),
      ih (start + 1) (by omega) (by omega)]
    have he : start + 1 + (n + 1) = start + (n + 2) := by omega
    simp only [he]
    have hne : (⟨start, by omega⟩ : Fin (r + 1)) ≠
        (⟨start + (n + 2), by omega⟩ : Fin (r + 1)) := by
      intro hh
      have hv := congrArg (fun i : Fin (r + 1) => i.val) hh
      dsimp only at hv
      omega
    have hs : (-1 : ℚ) ^ (n + 2 - 1) = -((-1 : ℚ) ^ n) := by
      rw [show n + 2 - 1 = n + 1 by omega, pow_succ, mul_neg_one]
    rw [hs, matrixUnit_neg]
    simpa only [negative, positive, Matrix.transpose_single] using
      matrixUnit_reverse_lie (⟨start, by omega⟩ : Fin (r + 1))
        ⟨start + 1, by omega⟩ ⟨start + (n + 2), by omega⟩ hne ((-1 : ℚ) ^ n)

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
