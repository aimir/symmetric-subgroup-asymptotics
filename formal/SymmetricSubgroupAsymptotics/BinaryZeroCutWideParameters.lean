import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact numerical parameters for a zero central cut at sufficiently
large binary pair degree. The middle-binomial recurrence propagates one
literal small inequality. No group, section, acceptance, or menu coverage
claim is made here; an actual invariant bound must be installed separately. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

/-- Pascal's identity and maximality of the middle coefficient give
the same doubling upper bound at both parities. -/
theorem binary_middle_succ_le_twice (k : ℕ) :
    (k+1).choose ((k+1)/2)≤2*k.choose (k/2) := by
  by_cases hk : k=0
  · subst k; decide
  · rw [Nat.choose_succ_left k ((k+1)/2) (by omega)]
    simpa only [two_mul] using Nat.add_le_add
      (Nat.choose_le_middle ((k+1)/2-1) k)
      (Nat.choose_le_middle ((k+1)/2) k)

/-- At k=11 the exact coefficient is 462; its normalized value and
all subsequent normalized middle widths are at most 15/64. -/
theorem binary_middle_le_fifteen_sixtyFourth (k : ℕ) (hk : 11≤k) :
    64*k.choose (k/2)≤15*2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    calc
      64*(k+1).choose ((k+1)/2)≤64*(2*k.choose (k/2)) :=
        Nat.mul_le_mul_left 64 (binary_middle_succ_le_twice k)
      _ = 2*(64*k.choose (k/2)) := by ring
      _ ≤ 2*(15*2^k) := Nat.mul_le_mul_left 2 ih
      _ = 15*2^(k+1) := by rw [pow_succ]; ring

/-- With pair degree s=2^k, physical width w=2s and zero-cut prefix
v=s, the exact natural gap w-v-4r is positive and is at least w/32.
The prefix also satisfies the direct wide-row requirement 16v≤13w. -/
theorem binary_zeroCut_wide_parameters_nat (k r : ℕ) (hk : 11≤k)
    (hr : r≤k.choose (k/2)) :
    16*(2^k)≤13*(2*2^k) ∧
      2*2^k≤32*((2*2^k)-2^k-4*r) ∧
      2^k+4*r<2*2^k := by
  have hwidth := binary_middle_le_fifteen_sixtyFourth k hk
  have hr' : 64*r≤15*2^k :=
    (Nat.mul_le_mul_left 64 hr).trans hwidth
  have hp : 0<2^k := pow_pos (by decide) _
  omega

/-- The same inequalities in real arithmetic permit an actual Schur
capacity r. Only its proved bound by the middle width is used. -/
theorem binary_zeroCut_wide_parameters (k : ℕ) (hk : 11≤k)
    (r : ℝ) (hr : r≤(k.choose (k/2) : ℝ)) :
    (2:ℝ)^k≤13*(2*(2:ℝ)^k)/16 ∧
      (2*(2:ℝ)^k)/32≤2*(2:ℝ)^k-(2:ℝ)^k-4*r ∧
      (2:ℝ)^k+4*r<2*(2:ℝ)^k := by
  have hwidth : (64:ℝ)*(k.choose (k/2) : ℝ)≤15*(2:ℝ)^k := by
    exact_mod_cast binary_middle_le_fifteen_sixtyFourth k hk
  have hp : 0<(2:ℝ)^k := pow_pos (by norm_num) _
  constructor
  · linarith
  constructor <;> linarith

/-- The associated direct-row gap parameter e=(w-v-4r)/16 is
strictly positive and meets the precise 16e≥w/32 requirement. -/
theorem binary_zeroCut_direct_gap (k : ℕ) (hk : 11≤k)
    (r : ℝ) (hr : r≤(k.choose (k/2) : ℝ)) :
    0<(2*(2:ℝ)^k-(2:ℝ)^k-4*r)/16 ∧
      (2*(2:ℝ)^k)/32≤16*((2*(2:ℝ)^k-(2:ℝ)^k-4*r)/16) := by
  obtain ⟨_,hgap,hstrict⟩ := binary_zeroCut_wide_parameters k hk r hr
  constructor <;> linarith

end SymmetricSubgroupAsymptotics
