import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalJacobi
import Lean.Elab.Tactic.Omega

/-! Right-nested interval brackets and their far/right-end actions.
These Lie identities do not assume a faithful matrix realization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalBrackets
variable {L : Type} [LieRing L]

def chainBracket (x : ℕ → L) (start n : ℕ) : L :=
  match n with
  | 0 => 0
  | 1 => x start
  | n + 2 => ⁅x start, chainBracket x (start + 1) (n + 1)⁆
termination_by n

theorem chainBracket_zero (x : ℕ → L) (start : ℕ) : chainBracket x start 0 = 0 := by
  rw [chainBracket]
theorem chainBracket_one (x : ℕ → L) (start : ℕ) : chainBracket x start 1 = x start := by
  rw [chainBracket]
theorem chainBracket_step (x : ℕ → L) (start n : ℕ) :
    chainBracket x start (n + 2) = ⁅x start, chainBracket x (start + 1) (n + 1)⁆ := by
  rw [chainBracket]

theorem lie_chainBracket_zero_of_each (x : ℕ → L) (a : L) (start n : ℕ)
    (h : ∀ j, start ≤ j → j < start + n → ⁅a, x j⁆ = 0) :
    ⁅a, chainBracket x start n⁆ = 0 := by
  induction n using Nat.twoStepInduction generalizing start with
  | zero => rw [chainBracket_zero, lie_zero]
  | one => rw [chainBracket_one]; exact h start le_rfl (by omega)
  | more n _ ih =>
    rw [chainBracket_step, leibniz_lie, h start le_rfl (by omega), zero_lie, zero_add]
    have ht : ⁅a, chainBracket x (start + 1) (n + 1)⁆ = 0 :=
      ih (start + 1) (fun j hj hj' => h j (by omega) (by omega))
    rw [ht, lie_zero]

theorem lie_chainBracket_far (x : ℕ → L)
    (hfar : ∀ i j, i + 1 < j ∨ j + 1 < i → ⁅x i, x j⁆ = 0)
    (k start n : ℕ) (hgap : k + 1 < start ∨ start + n < k) :
    ⁅x k, chainBracket x start n⁆ = 0 :=
  lie_chainBracket_zero_of_each x (x k) start n
    (fun j hj hj' => hfar k j (by omega))

theorem lie_chainBracket_right (x : ℕ → L)
    (hfar : ∀ i j, i + 1 < j ∨ j + 1 < i → ⁅x i, x j⁆ = 0)
    (start n : ℕ) (hn : 0 < n) :
    ⁅x (start + n), chainBracket x start n⁆ = -chainBracket x start (n + 1) := by
  induction n using Nat.twoStepInduction generalizing start with
  | zero => omega
  | one =>
    rw [chainBracket_one, chainBracket_step, chainBracket_one]
    exact (lie_skew _ _).symm
  | more n _ ih =>
    rw [chainBracket_step, leibniz_lie,
      hfar (start + (n + 2)) start (by omega), zero_lie, zero_add]
    have ht : ⁅x (start + (n + 2)), chainBracket x (start + 1) (n + 1)⁆ =
        -chainBracket x (start + 1) (n + 2) := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (start + 1) (by omega)
    rw [ht, lie_neg, chainBracket_step x start (n + 1)]

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalBrackets
