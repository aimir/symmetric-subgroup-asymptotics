import SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusExponentPilot
import Mathlib.Tactic.Linarith

/-! Every ambient E6 root has a nontrivial fixed-torus exponent modulo
q-1 for ReeF4 q>2. The q=8 boundary is the separate finite certificate;
for larger q the bounded integer coefficients lie strictly inside the
unit-group modulus. No conjugation or derived-group claim occurs here. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusExponents
open CFSGNormTwoRootPairing CFSGReeFFourRootTorusExponentPilot

def firstExponent (m : ℕ) (x : Fin 6→ℤ) : ℤ :=
  firstBase x+(2 : ℤ)^(m+1)*firstAlpha x
def secondExponent (m : ℕ) (x : Fin 6→ℤ) : ℤ :=
  secondBase x+(2 : ℤ)^(m+1)*secondAlpha x

private theorem zero_of_dvd_of_bounds (n x : ℤ) (hlo : -n<x) (hhi : x<n)
    (hdiv : n∣x) : x=0 := by
  by_cases hx : 0≤x
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hx hhi hdiv
  · have hneg : -x=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt
      (by omega) (by omega) (dvd_neg.mpr hdiv)
    omega

private theorem linear_form_zero (t n p q : ℤ) (ht : 4≤t)
    (hn : 2+2*t<n) (hp : -2≤p ∧ p≤2) (hq : -2≤q ∧ q≤2)
    (hdiv : n∣p+t*q) : p=0 ∧ q=0 := by
  have ht0 : 0≤t := by omega
  have hl := mul_le_mul_of_nonneg_left hq.1 ht0
  have hh := mul_le_mul_of_nonneg_left hq.2 ht0
  have he : p+t*q=0 := zero_of_dvd_of_bounds n (p+t*q) (by nlinarith) (by nlinarith) hdiv
  have hqzero : q=0 := by
    by_contra hzero
    rcases lt_or_gt_of_ne hzero with hneg|hpos
    · have hh' := mul_le_mul_of_nonneg_left (show q≤-1 by omega) ht0
      nlinarith
    · have hl' := mul_le_mul_of_nonneg_left (show 1≤q by omega) ht0
      nlinarith
  exact ⟨by simpa only [hqzero,mul_zero,add_zero] using he,hqzero⟩

private theorem modulus_bound (m : ℕ) (hm : 2≤m) :
    2+2*(2 : ℤ)^(m+1)<(2 : ℤ)^(2*m+1)-1 := by
  have h4 : (4 : ℤ)≤2^m := by
    have h := pow_le_pow_right₀ (by decide : (1 : ℤ)≤2) hm
    norm_num at h
    exact h
  have h8 : (8 : ℤ)≤2^(m+1) := by
    have h := pow_le_pow_right₀ (by decide : (1 : ℤ)≤2) (show 3≤m+1 by omega)
    norm_num at h
    exact h
  have he : (2 : ℤ)^(2*m+1)=(2 : ℤ)^(m+1)*(2 : ℤ)^m := by
    rw [←pow_add]
    congr 1
    omega
  rw [he]
  have hh := mul_le_mul_of_nonneg_left h4 (show (0 : ℤ)≤2^(m+1) by positivity)
  nlinarith

theorem root_exponent_nondivisible (m : ℕ) (hm : 0<m) (k : Roots CartanMatrix.E₆) :
    ¬(((2 : ℤ)^(2*m+1)-1)∣firstExponent m k.val) ∨
      ¬(((2 : ℤ)^(2*m+1)-1)∣secondExponent m k.val) := by
  by_cases hsmall : m=1
  · subst m
    simpa only [firstExponent,secondExponent] using root_eight_exponents_nondivisible k
  · have hm2 : 2≤m := by omega
    by_contra hboth
    have hb : (((2 : ℤ)^(2*m+1)-1)∣firstExponent m k.val) ∧
        (((2 : ℤ)^(2*m+1)-1)∣secondExponent m k.val) := by
      simpa only [not_or,not_not] using hboth
    obtain ⟨hpa,hqa,hpb,hqb⟩ := root_exponent_bounds k
    have ht : (4 : ℤ)≤2^(m+1) := by
      have h := pow_le_pow_right₀ (by decide : (1 : ℤ)≤2) (show 2≤m+1 by omega)
      norm_num at h
      exact h
    have ha := linear_form_zero ((2 : ℤ)^(m+1)) ((2 : ℤ)^(2*m+1)-1)
      (firstBase k.val) (firstAlpha k.val) ht (modulus_bound m hm2) hpa hqa hb.1
    have hb' := linear_form_zero ((2 : ℤ)^(m+1)) ((2 : ℤ)^(2*m+1)-1)
      (secondBase k.val) (secondAlpha k.val) ht (modulus_bound m hm2) hpb hqb hb.2
    exact root_exponents_nonzero k ⟨ha.1,ha.2,hb'.1,hb'.2⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusExponents
