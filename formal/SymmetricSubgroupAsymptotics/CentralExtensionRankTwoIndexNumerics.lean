import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Cancellation of the correlated central/vector orbit bounds.
The inputs are the exact subgroup cardinal identity, central properness,
isotropy, and the two actual layer orbits, rather than an index bound
for an independently chosen projected stabilizer. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CentralExtensionRankTwoIndexNumerics

theorem index_trichotomy (p q g m c w l : ℕ) (hq : 2 ≤ q)
    (hc : 0 < c) (hw : 0 < w) (hl : 0 < l)
    (hcentral : p * c ≤ q) (hisotropic : w ≤ q)
    (hexact : m * c * w = q ^ 3 * l)
    (hvector : 1 < w → q ^ 2 - 1 ≤ g * (w - 1) * l)
    (hcentre : 1 < c → q - 1 ≤ (c - 1) * l) :
    q ^ 3 ≤ m ∨ p ^ 2 * q * (q - 1) ≤ m ∨ p * q * (q + 1) ≤ g * m := by
  by_cases hw1 : w = 1
  · subst w
    simp only [mul_one] at hexact
    by_cases hc1 : c = 1
    · subst c
      simp only [mul_one] at hexact
      exact Or.inl (by nlinarith)
    · right
      left
      have hcgt : 1 < c := by omega
      have hcc : p ^ 2 * c * (c - 1) ≤ q ^ 2 := by
        calc
          _ ≤ (p * c) ^ 2 := by
            have ht := Nat.mul_le_mul_left (p ^ 2 * c) (Nat.sub_le c 1)
            nlinarith
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hcentral 2
      have hraw := Nat.mul_le_mul_left (p ^ 2 * q ^ 3) (hcentre hcgt)
      have hbound : p ^ 2 * q * (q - 1) * q ^ 2 ≤ m * q ^ 2 := by
        calc
          _ = (p ^ 2 * q ^ 3) * (q - 1) := by ring
          _ ≤ (p ^ 2 * q ^ 3) * ((c - 1) * l) := hraw
          _ = p ^ 2 * (c - 1) * (q ^ 3 * l) := by ring
          _ = p ^ 2 * (c - 1) * (m * c) := by rw [← hexact]
          _ = m * (p ^ 2 * c * (c - 1)) := by ring
          _ ≤ m * q ^ 2 := Nat.mul_le_mul_left m hcc
      exact Nat.le_of_mul_le_mul_right hbound (pow_pos (by omega) 2)
  · right
    right
    have hwgt : 1 < w := by omega
    have hqfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have hsub := Nat.sub_add_cancel (show 1 ≤ q by omega)
      have hsub2 := Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)
      nlinarith
    have hcw : p * c * w * (w - 1) ≤ q ^ 2 * (q - 1) := by
      have hww : w * (w - 1) ≤ q * (q - 1) :=
        Nat.mul_le_mul hisotropic (Nat.sub_le_sub_right hisotropic 1)
      have ht := Nat.mul_le_mul hcentral hww
      nlinarith
    have hraw := Nat.mul_le_mul_left (p * q ^ 3) (hvector hwgt)
    have hbound : p * q * (q + 1) * (q ^ 2 * (q - 1)) ≤
        g * m * (q ^ 2 * (q - 1)) := by
      calc
        _ = (p * q ^ 3) * (q ^ 2 - 1) := by rw [hqfactor]; ring
        _ ≤ (p * q ^ 3) * (g * (w - 1) * l) := hraw
        _ = p * g * (w - 1) * (q ^ 3 * l) := by ring
        _ = p * g * (w - 1) * (m * c * w) := by rw [← hexact]
        _ = g * m * (p * c * w * (w - 1)) := by ring
        _ ≤ g * m * (q ^ 2 * (q - 1)) := Nat.mul_le_mul_left (g * m) hcw
    exact Nat.le_of_mul_le_mul_right hbound
      (Nat.mul_pos (pow_pos (by omega) 2) (by omega))

end SymmetricSubgroupAsymptotics.CentralExtensionRankTwoIndexNumerics
