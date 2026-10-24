import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The characteristic-prime factor justified by a nonabelian central
extension with an isotropic quotient image. This is not a bound for an
abelian radical. All cardinal factors come from one stabilizer. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CentralExtensionIsotropicOrbitNumerics

theorem prime_mul_orbit_le_index (p q v m c w l O : ℕ)
    (hq : 0 < q) (hv : 0 < v) (hc : 0 < c) (hw : 0 < w) (hl : 0 < l)
    (hcentral : p * c ≤ q) (hisotropic : w ≤ v)
    (hexact : m * c * w = q * v ^ 2 * l) (hO : O ≤ v ^ 2)
    (horbit : 1 < w → O ≤ (w - 1) * l) : p * O ≤ m := by
  by_cases hw1 : w = 1
  · subst w
    simp only [mul_one] at hexact
    have hbound : p * v ^ 2 * c ≤ m * c := by
      calc
        _ = (p * c) * v ^ 2 := by ring
        _ ≤ q * v ^ 2 := Nat.mul_le_mul_right (v ^ 2) hcentral
        _ ≤ q * v ^ 2 * l := by
          simpa only [mul_one] using Nat.mul_le_mul_left (q * v ^ 2) (show 1 ≤ l by omega)
        _ = _ := hexact.symm
    exact (Nat.mul_le_mul_left p hO).trans (Nat.le_of_mul_le_mul_right hbound hc)
  · have hwgt : 1 < w := by omega
    have ho : O ≤ w * l := (horbit hwgt).trans
      (Nat.mul_le_mul_right l (Nat.sub_le w 1))
    have hcw : (p * c) * w ^ 2 ≤ q * v ^ 2 :=
      Nat.mul_le_mul hcentral (Nat.pow_le_pow_left hisotropic 2)
    have hbound : p * O * (q * v ^ 2) ≤ m * (q * v ^ 2) := by
      calc
        _ ≤ p * (w * l) * (q * v ^ 2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left p ho)
        _ = p * w * (q * v ^ 2 * l) := by ring
        _ = p * w * (m * c * w) := by rw [← hexact]
        _ = m * ((p * c) * w ^ 2) := by ring
        _ ≤ m * (q * v ^ 2) := Nat.mul_le_mul_left m hcw
    exact Nat.le_of_mul_le_mul_right hbound (Nat.mul_pos hq (pow_pos hv 2))

end SymmetricSubgroupAsymptotics.CentralExtensionIsotropicOrbitNumerics
