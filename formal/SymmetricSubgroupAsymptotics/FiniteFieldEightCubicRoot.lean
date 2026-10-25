import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The selected bit-field polynomial has an actual root in every field
of cardinal eight. The construction uses a literal order-seven unit,
the two reciprocal cubic factors, and no chosen finite-field model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteFieldEightCubicRoot

variable (K : Type*) [Field K] [Finite K] [CharP K 2]

theorem exists_cubic_root (hcard : Nat.card K = 8) :
    ∃ x : K, x^3+x+1 = 0 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
  have hd : 7 ∣ Nat.card Kˣ := by rw [Nat.card_units,hcard]
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 7 hd
  let x : K := u
  have hx0 : x ≠ 0 := Units.ne_zero u
  have hx1 : x ≠ 1 := by
    intro he
    have hu1 : u = 1 := Units.ext he
    rw [hu1,orderOf_one] at hu
    exact (by decide : (1 : ℕ) ≠ 7) hu
  have hpow : x^7 = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    exact congrArg (fun a : Kˣ => (a : K)) h
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hfac : (x+1)*((x^3+x+1)*(x^3+x^2+1)) = x^7+1 := by
    linear_combination (x^6+x^5+2*x^4+2*x^3+x^2+x)*htwo
  have hplus : x+1 ≠ 0 := by
    intro h
    apply hx1
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
  have hprod : (x^3+x+1)*(x^3+x^2+1) = 0 := by
    apply (mul_eq_zero.mp (show (x+1)*((x^3+x+1)*(x^3+x^2+1)) = 0 from
      hfac.trans (by rw [hpow]; exact CharTwo.add_self_eq_zero 1))).resolve_left hplus
  rcases mul_eq_zero.mp hprod with hf | hg
  · exact ⟨x,hf⟩
  · refine ⟨x⁻¹,?_⟩
    apply (mul_eq_zero.mp (show x^3*((x⁻¹)^3+x⁻¹+1) = 0 from ?_)).resolve_left
      (pow_ne_zero 3 hx0)
    calc
      _ = x^3+x^2+1 := by field_simp [hx0] <;> ring
      _ = 0 := hg

end SymmetricSubgroupAsymptotics.FiniteFieldEightCubicRoot
