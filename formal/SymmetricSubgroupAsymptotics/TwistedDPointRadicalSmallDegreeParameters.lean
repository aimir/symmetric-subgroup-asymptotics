import Mathlib.Tactic.NormNum

/-! The literal twisted-D point-radical lower bound below32 forces the
binary rank-four parameters, without a list of groups or actions. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TwistedDPointRadicalSmallDegreeParameters

theorem parameters (s q r : ℕ) (hq : 2 ≤ q)
    (hindex : (q^(s+2)-1)*q^(s+3) ≤ r) (hsmall : r < 32) :
    s = 0 ∧ q = 2 ∧ 24 ≤ r := by
  have hqpos : 0 < q := by omega
  have hs : s = 0 := by
    by_contra hh
    have hleft : 8 ≤ q^(s+2) :=
      (Nat.pow_le_pow_left hq 3).trans (Nat.pow_le_pow_right hqpos (by omega))
    have hright : 16 ≤ q^(s+3) :=
      (Nat.pow_le_pow_left hq 4).trans (Nat.pow_le_pow_right hqpos (by omega))
    have hprod : 112 ≤ (q^(s+2)-1)*q^(s+3) := by
      calc
        112 = (8-1)*16 := by decide
        _ ≤ (q^(s+2)-1)*q^(s+3) := Nat.mul_le_mul (by omega) hright
    omega
  subst s
  have hq2 : q = 2 := by
    by_contra hh
    have hq3 : 3 ≤ q := by omega
    have hleft : 9 ≤ q^(0+2) := Nat.pow_le_pow_left hq3 2
    have hright : 27 ≤ q^(0+3) := Nat.pow_le_pow_left hq3 3
    have hprod : 216 ≤ (q^(0+2)-1)*q^(0+3) := by
      calc
        216 = (9-1)*27 := by decide
        _ ≤ (q^(0+2)-1)*q^(0+3) := Nat.mul_le_mul (by omega) hright
    omega
  subst q
  norm_num at hindex
  exact ⟨rfl,rfl,hindex⟩

end SymmetricSubgroupAsymptotics.TwistedDPointRadicalSmallDegreeParameters
