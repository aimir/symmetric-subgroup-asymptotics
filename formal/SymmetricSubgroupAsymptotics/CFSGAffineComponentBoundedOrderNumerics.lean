import SymmetricSubgroupAsymptotics.CFSGAffineComponentIntegerMargin

/-! Bounded prime-power arithmetic for the actual full affine order.
This checks integers, not a catalogue of groups or actions. Degree32 is
excluded because its faithful irreducible complement requires the separate
Clifford argument. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

theorem fullAffine_component_integer_budget_bounded {p d : ℕ}
    (hp : p.Prime) (hd : 2 ≤ d) (hlow : 25 ≤ p^d)
    (hhi : p^d < 1024) (hne32 : p^d ≠ 32) :
    54272*ArithmeticFunction.cardFactors (fullAffineOrder p d)+38400 ≤ 25575*p^d := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp31 : p ≤ 31 := by
    have hsq : p^2 < 1024 := (Nat.pow_le_pow_right hp.pos hd).trans_lt hhi
    nlinarith
  have hd9 : d ≤ 9 := by
    by_contra h
    have hd10 : 10 ≤ d := by omega
    have hlarge : 2^10 ≤ p^d :=
      (Nat.pow_le_pow_left hp2 10).trans (Nat.pow_le_pow_right hp.pos hd10)
    norm_num at hlarge
    omega
  interval_cases p <;> interval_cases d
  all_goals norm_num at hp
  all_goals norm_num at hlow
  all_goals norm_num at hhi
  all_goals norm_num at hne32
  all_goals unfold fullAffineOrder fullLinearOrder
  all_goals decide +kernel

end SymmetricSubgroupAsymptotics
