import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! Arithmetic of the two ordinary nonaffine primitive degree forms.
This file assumes no classification, socle profile, or outer-group input. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

/-- Product action, or diagonal/twisted-wreath degree with at most twice
as many simple factors as the exponent of the simple-group order. -/
def PrimitiveSocleDegreeForm (ell orderT k r : ℕ) : Prop :=
  (∃ a : ℕ,ell ≤ a ∧ r=a^k) ∨
    (∃ a : ℕ,k ≤ 2*a ∧ r=orderT^a)

theorem primitiveSocle_power_le_degree {ell orderT k r : ℕ}
    (hell : 5 ≤ ell) (horder : ell^2 < orderT)
    (hform : PrimitiveSocleDegreeForm ell orderT k r) : ell^k ≤ r := by
  rcases hform with ⟨a,ha,rfl⟩ | ⟨a,hk,rfl⟩
  · exact Nat.pow_le_pow_left ha k
  · calc
      ell^k ≤ ell^(2*a) := Nat.pow_le_pow_right (by omega) hk
      _ = (ell^2)^a := pow_mul ell 2 a
      _ ≤ orderT^a := Nat.pow_le_pow_left horder.le a

theorem primitiveSocle_degree_five_le {ell orderT k r : ℕ}
    (hell : 5 ≤ ell) (horder : ell^2 < orderT) (hk : 0 < k)
    (hform : PrimitiveSocleDegreeForm ell orderT k r) : 5 ≤ r := by
  have hpow := primitiveSocle_power_le_degree hell horder hform
  have he : ell ≤ ell^k := by
    calc
      ell=ell^1 := (pow_one ell).symm
      _ ≤ ell^k := Nat.pow_le_pow_right (by omega) hk
  omega

theorem primitiveSocle_degree_pos {ell orderT k r : ℕ}
    (hell : 5 ≤ ell) (horder : ell^2 < orderT) (hk : 0 < k)
    (hform : PrimitiveSocleDegreeForm ell orderT k r) : 0 < r := by
  have := primitiveSocle_degree_five_le hell horder hk hform
  omega

end SymmetricSubgroupAsymptotics
