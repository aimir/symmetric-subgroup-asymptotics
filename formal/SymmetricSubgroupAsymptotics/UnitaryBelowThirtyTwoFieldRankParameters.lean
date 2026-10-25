import Mathlib.Tactic.NormNum

/-! Literal q^rank<32 with the classifier's rank-two guard leaves six
unitary field/rank parameter pairs. This is elementary parameter
arithmetic, not a completeness claim about finite actions. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.UnitaryBelowThirtyTwoFieldRankParameters

theorem parameters (r q : ℕ) (hr : 2 ≤ r) (hq : 2 ≤ q)
    (hs : r = 2 → q ≠ 2) (hsmall : q^r < 32) :
    (r = 2 ∧ (q = 3 ∨ q = 4 ∨ q = 5)) ∨
      (r = 3 ∧ (q = 2 ∨ q = 3)) ∨ (r = 4 ∧ q = 2) := by
  have hr4 : r ≤ 4 := by
    by_contra hh
    have h1 := Nat.pow_le_pow_left hq r
    have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ r by omega)
    norm_num at h2
    omega
  have hrCases : r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hrCases with rfl | rfl | rfl
  · left
    refine ⟨rfl,?_⟩
    have hq5 : q ≤ 5 := by
      by_contra hh
      have hp := Nat.pow_le_pow_left (show 6 ≤ q by omega) 2
      norm_num at hp
      omega
    have hne := hs rfl
    omega
  · right; left
    refine ⟨rfl,?_⟩
    have hq3 : q ≤ 3 := by
      by_contra hh
      have hp := Nat.pow_le_pow_left (show 4 ≤ q by omega) 3
      norm_num at hp
      omega
    omega
  · right; right
    refine ⟨rfl,?_⟩
    by_contra hh
    have hp := Nat.pow_le_pow_left (show 3 ≤ q by omega) 4
    norm_num at hp
    omega

end SymmetricSubgroupAsymptotics.UnitaryBelowThirtyTwoFieldRankParameters
