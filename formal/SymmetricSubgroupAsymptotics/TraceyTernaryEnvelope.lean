import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Literal ternary numerical envelope from Tracey, Definition 1.5.

This file proves arithmetic of E(s,3), not an induced-module theorem.
The latter needs its exact published hypotheses and the actual module.
In particular we do not assert the real inequality E_sol ≤ E: with the
unfloored definition of tilde-omega printed in the source that inequality
is false already at s=3. The prime-power induced-module bound supplies a
separate valid route to the general E envelope.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- Largest prime-power divisor, with the source convention lpp(1)=1. -/
def largestPrimePower (n : ℕ) : ℕ :=
  max 1 (n.factorization.support.sup (fun p => p^n.factorization p))

theorem largestPrimePower_pos (n : ℕ) : 0<largestPrimePower n := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem primePower_le_largestPrimePower (n p : ℕ) :
    p^n.factorization p≤largestPrimePower n := by
  by_cases hp : n.factorization p=0
  · simp [hp,largestPrimePower]
  · exact (Finset.le_sup (f:=fun q => q^n.factorization q)
      (Finsupp.mem_support_iff.mpr hp)).trans (le_max_right _ _)

/-- A prime-to-three integer other than one or two has a prime-power
divisor of size at least four. No factorization catalogue is used. -/
theorem largestPrimePower_ge_four (n : ℕ) (hn : n≠0) (h3 : ¬3∣n)
    (h1 : n≠1) (h2 : n≠2) : 4≤largestPrimePower n := by
  by_contra h
  have hl : largestPrimePower n≤3 := by omega
  have hd : n∣2 := (Nat.factorization_le_iff_dvd hn (by decide)).mp (by
    intro p
    by_cases hp0 : n.factorization p=0
    · simp [hp0]
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors
      (show p∈n.primeFactors from Finsupp.mem_support_iff.mpr hp0)
    have hpv : p^n.factorization p≤3 := (primePower_le_largestPrimePower n p).trans hl
    have hple : p≤3 := (Nat.le_self_pow (by omega : n.factorization p≠0) p).trans hpv
    have hp2 : p=2 := by
      have hpge := hpp.two_le
      have hp3 : p≠3 := by
        intro hp3; subst p
        exact h3 (Nat.dvd_of_factorization_pos hp0)
      omega
    subst p
    have he : n.factorization 2≤1 := by
      by_contra he
      have hpow : 2^2≤2^n.factorization 2 := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at hpow
      omega
    simpa [(by decide : Nat.Prime 2).factorization_self] using he)
  have hnle : n≤2 := Nat.le_of_dvd (by decide) hd
  omega

/-- The first branch is omitted when the ternary valuation is zero,
matching the source's infinite-entry convention. -/
def traceyTernaryEnvelope (s : ℕ) : ℝ :=
  if s.factorization 3=0 then
    (s:ℝ)/largestPrimePower (ordCompl[3] s)
  else min (⌊(s:ℝ)/Real.sqrt (Real.pi*(s.factorization 3:ℝ))⌋₊:ℝ)
    ((s:ℝ)/largestPrimePower (ordCompl[3] s))

theorem traceyTernaryEnvelope_nonneg (s : ℕ) : 0≤traceyTernaryEnvelope s := by
  unfold traceyTernaryEnvelope
  split_ifs <;> positivity

theorem traceyTernaryEnvelope_le_coprime (s : ℕ) :
    traceyTernaryEnvelope s≤(s:ℝ)/largestPrimePower (ordCompl[3] s) := by
  unfold traceyTernaryEnvelope
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

theorem traceyTernaryEnvelope_le_gaussian (s : ℕ) (hk : s.factorization 3≠0) :
    traceyTernaryEnvelope s≤(s:ℝ)/Real.sqrt (Real.pi*(s.factorization 3:ℝ)) := by
  unfold traceyTernaryEnvelope
  rw [if_neg hk]
  exact (min_le_left _ _).trans (Nat.floor_le (by positivity))

theorem traceyTernaryEnvelope_le_floor (s : ℕ) (hk : s.factorization 3≠0) :
    traceyTernaryEnvelope s≤(⌊(s:ℝ)/Real.sqrt (Real.pi*(s.factorization 3:ℝ))⌋₊:ℝ) := by
  simp only [traceyTernaryEnvelope,if_neg hk]
  exact min_le_left _ _

theorem traceyTernaryEnvelope_le_quarter (s : ℕ) (hs : s≠0)
    (h1 : ordCompl[3] s≠1) (h2 : ordCompl[3] s≠2) :
    traceyTernaryEnvelope s≤(s:ℝ)/4 := by
  have hl := largestPrimePower_ge_four (ordCompl[3] s)
    (Nat.ordCompl_pos 3 hs).ne' (Nat.not_dvd_ordCompl (by decide) hs) h1 h2
  exact (traceyTernaryEnvelope_le_coprime s).trans
    (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by exact_mod_cast hl))

theorem traceyTernaryEnvelope_tail (s : ℕ) (hk : 3≤s.factorization 3) :
    traceyTernaryEnvelope s≤(s:ℝ)/3 := by
  have hpi := Real.pi_gt_three
  have hk' : (3:ℝ)≤s.factorization 3 := by exact_mod_cast hk
  have hsq : (3:ℝ)≤Real.sqrt (Real.pi*(s.factorization 3:ℝ)) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  exact (traceyTernaryEnvelope_le_gaussian s (by omega)).trans
    (div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq)

theorem traceyTernaryEnvelope_floor_bound (s e : ℕ)
    (hk : s.factorization 3≠0)
    (h : (s:ℝ)^2<(e+1:ℝ)^2*(Real.pi*(s.factorization 3:ℝ))) :
    traceyTernaryEnvelope s≤e := by
  have hz : 0<Real.pi*(s.factorization 3:ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hz.le
  have hsqrt0 := Real.sqrt_pos.mpr hz
  have he0 : (0:ℝ)<e+1 := by positivity
  have hq : (s:ℝ)<(e+1:ℝ)*Real.sqrt (Real.pi*(s.factorization 3:ℝ)) := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rwa [mul_pow,hsqrt]
  have hlt : (s:ℝ)/Real.sqrt (Real.pi*(s.factorization 3:ℝ))<((e+1:ℕ):ℝ) := by
    push_cast
    exact (div_lt_iff₀ hsqrt0).mpr hq
  have hfloor : ⌊(s:ℝ)/Real.sqrt (Real.pi*(s.factorization 3:ℝ))⌋₊≤e :=
    Nat.lt_succ_iff.mp ((Nat.floor_lt (by positivity)).mpr hlt)
  exact (traceyTernaryEnvelope_le_floor s hk).trans (by exact_mod_cast hfloor)

theorem traceyTernaryEnvelope_three : traceyTernaryEnvelope 3≤1 := by
  have hf : (3:ℕ).factorization 3=1 := (by decide : Nat.Prime 3).factorization_self
  have hb := traceyTernaryEnvelope_floor_bound 3 1 (by omega)
  norm_num at hb
  apply hb
  have := Real.pi_gt_three
  linarith

theorem traceyTernaryEnvelope_six : traceyTernaryEnvelope 6≤3 := by
  have hf : (6:ℕ).factorization 3=1 := by
    rw [show 6=2*3 by rfl,Nat.factorization_mul (by decide) (by decide)]
    norm_num [(by decide : Nat.Prime 2).factorization,(by decide : Nat.Prime 3).factorization]
  apply traceyTernaryEnvelope_floor_bound 6 3 (by omega)
  rw [hf]
  have := Real.pi_gt_three
  norm_num
  linarith

theorem traceyTernaryEnvelope_nine : traceyTernaryEnvelope 9≤3 := by
  have hf : (9:ℕ).factorization 3=2 := by
    simpa using Nat.factorization_pow_self (by decide : Nat.Prime 3) (n:=2)
  apply traceyTernaryEnvelope_floor_bound 9 3 (by omega)
  rw [hf]
  have := Real.pi_gt_three
  norm_num
  linarith

theorem traceyTernaryEnvelope_eighteen : traceyTernaryEnvelope 18≤7 := by
  have hf9 : (9:ℕ).factorization 3=2 := by
    simpa using Nat.factorization_pow_self (by decide : Nat.Prime 3) (n:=2)
  have hf : (18:ℕ).factorization 3=2 := by
    rw [show 18=2*9 by rfl,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 2).factorization,hf9]
  apply traceyTernaryEnvelope_floor_bound 18 7 (by omega)
  rw [hf]
  have := Real.pi_gt_three
  norm_num
  linarith

/-- All ordinary top degrees are eliminated together. -/
theorem traceyTernaryEnvelope_ordinary (s : ℕ) (hs : 2≤s)
    (h2 : s≠2) (h6 : s≠6) (h18 : s≠18) :
    traceyTernaryEnvelope s≤(s:ℝ)/3 := by
  by_cases ht1 : ordCompl[3] s=1
  · have hpow : 3^s.factorization 3=s := by
      simpa [ht1] using Nat.ordProj_mul_ordCompl_eq_self s 3
    by_cases hk : 3≤s.factorization 3
    · exact traceyTernaryEnvelope_tail s hk
    interval_cases he : s.factorization 3
    · norm_num [he] at hpow; omega
    · norm_num [he] at hpow
      subst s
      simpa using traceyTernaryEnvelope_three
    · norm_num [he] at hpow
      subst s
      convert traceyTernaryEnvelope_nine using 1
      norm_num
  · by_cases ht2 : ordCompl[3] s=2
    · have hpow : 3^s.factorization 3*2=s := by
        simpa [ht2] using Nat.ordProj_mul_ordCompl_eq_self s 3
      by_cases hk : 3≤s.factorization 3
      · exact traceyTernaryEnvelope_tail s hk
      interval_cases he : s.factorization 3 <;> norm_num [he] at hpow <;> omega
    · exact (traceyTernaryEnvelope_le_quarter s (by omega) ht1 ht2).trans
        (by linarith [Nat.cast_nonneg (α:=ℝ) s])

theorem traceyTernaryEnvelope_ten_twentyseven (s : ℕ) (hs : 2≤s)
    (h2 : s≠2) (h6 : s≠6) (h18 : s≠18) :
    traceyTernaryEnvelope s≤10*(s:ℝ)/27 :=
  (traceyTernaryEnvelope_ordinary s hs h2 h6 h18).trans
    (by linarith [Nat.cast_nonneg (α:=ℝ) s])

theorem traceyTernaryEnvelope_seven_eighteen (s : ℕ) (hs : 2≤s)
    (h2 : s≠2) (h6 : s≠6) : traceyTernaryEnvelope s≤7*(s:ℝ)/18 := by
  by_cases h18 : s=18
  · subst s; simpa using traceyTernaryEnvelope_eighteen
  · exact (traceyTernaryEnvelope_ordinary s hs h2 h6 h18).trans
      (by linarith [Nat.cast_nonneg (α:=ℝ) s])

theorem traceyTernaryEnvelope_high_valuation (s : ℕ) (hk : 5≤s.factorization 3) :
    traceyTernaryEnvelope s≤143*(s:ℝ)/540 := by
  have hk' : (5:ℝ)≤s.factorization 3 := by exact_mod_cast hk
  have hpi := Real.pi_gt_three
  have hsq : (540/143:ℝ)≤Real.sqrt (Real.pi*(s.factorization 3:ℝ)) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  calc
    traceyTernaryEnvelope s≤(s:ℝ)/Real.sqrt (Real.pi*(s.factorization 3:ℝ)) :=
      traceyTernaryEnvelope_le_gaussian s (by omega)
    _≤(s:ℝ)/(540/143) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq
    _=143*(s:ℝ)/540 := by ring

/-- The ordinary ternary-block numerical test leaves just nine literal
top degrees. The special small tops are deliberately still included in
this list; the actual group induction decides which rows use them. -/
theorem traceyTernaryEnvelope_ternary_block (s : ℕ) (hs : 2≤s)
    (hsmall : s∉({2,3,6,9,18,27,54,81,162}:Finset ℕ)) :
    traceyTernaryEnvelope s+5*(s:ℝ)/27≤9*(s:ℝ)/20 := by
  by_cases hk : 5≤s.factorization 3
  · have he := traceyTernaryEnvelope_high_valuation s hk
    linarith
  by_cases ht1 : ordCompl[3] s=1
  · have hpow : 3^s.factorization 3=s := by
      simpa [ht1] using Nat.ordProj_mul_ordCompl_eq_self s 3
    have hs' : s≠2 ∧ s≠3 ∧ s≠6 ∧ s≠9 ∧ s≠18 ∧ s≠27 ∧ s≠54 ∧ s≠81 ∧ s≠162 := by
      simpa using hsmall
    interval_cases he : s.factorization 3 <;> norm_num [he] at hpow <;> omega
  · by_cases ht2 : ordCompl[3] s=2
    · have hpow : 3^s.factorization 3*2=s := by
        simpa [ht2] using Nat.ordProj_mul_ordCompl_eq_self s 3
      have hs' : s≠2 ∧ s≠3 ∧ s≠6 ∧ s≠9 ∧ s≠18 ∧ s≠27 ∧ s≠54 ∧ s≠81 ∧ s≠162 := by
        simpa using hsmall
      interval_cases he : s.factorization 3 <;> norm_num [he] at hpow <;> omega
    · have he := traceyTernaryEnvelope_le_quarter s (by omega) ht1 ht2
      linarith [Nat.cast_nonneg (α:=ℝ) s]

end SymmetricSubgroupAsymptotics
