import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Elementary degree bands for an actual odd prime power below128.
Only primality, exponent monotonicity and scalar degree bounds are used;
there is no finite-group or action catalogue. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.OddPrimePowerSmallDimensionBands

theorem bands (p d r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : r = p^d) (hr11 : 11 ≤ r) (hr128 : r < 128) :
    d ≤ 1 ∨ (d ≤ 2 ∧ 25 ≤ r) ∨ (p = 3 ∧ d = 3) ∨ (d ≤ 4 ∧ 64 ≤ r) := by
  have hodd := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := hp.odd_iff.mp hodd
  have hlow (a b : ℕ) (ha : a ≤ p) (hb : b ≤ d) : a^b ≤ r := by
    exact ((Nat.pow_le_pow_left ha b).trans
      (Nat.pow_le_pow_right hp.pos hb)).trans_eq hr.symm
  have hd4 : d ≤ 4 := by
    by_contra hn
    have hh := hlow 3 5 hp3 (by omega)
    norm_num at hh
    omega
  by_cases h64 : 64 ≤ r
  · exact Or.inr (Or.inr (Or.inr ⟨hd4,h64⟩))
  have hr64 : r < 64 := by omega
  by_cases hd1 : d ≤ 1
  · exact Or.inl hd1
  have hd2 : 2 ≤ d := by omega
  by_cases hp_eq : p = 3
  · have hd3 : d ≤ 3 := by
      by_contra hn
      have hh := hlow 3 4 hp3 (by omega)
      norm_num at hh
      omega
    have hd_ne : d ≠ 2 := by
      intro he
      have hh : r = 9 := by simpa only [hp_eq,he] using hr
      omega
    exact Or.inr (Or.inr (Or.inl ⟨hp_eq,by omega⟩))
  · have hp5 : 5 ≤ p := by
      have hm := Nat.odd_iff.mp hodd
      omega
    have hd_le_two : d ≤ 2 := by
      by_contra hn
      have hh := hlow 5 3 hp5 (by omega)
      norm_num at hh
      omega
    have h25 : 25 ≤ r := by
      have hh := hlow 5 2 hp5 hd2
      exact hh
    exact Or.inr (Or.inl ⟨hd_le_two,h25⟩)

end SymmetricSubgroupAsymptotics.OddPrimePowerSmallDimensionBands
