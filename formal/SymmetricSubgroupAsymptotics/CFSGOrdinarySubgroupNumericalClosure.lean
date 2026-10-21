import SymmetricSubgroupAsymptotics.CFSGOrdinaryBoundedNilpotentFormula
import SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupUpperNumerics
import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersRate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Numerical closure of the actual finite convolution. The only counting
estimate supplied to this internal theorem concerns the strictly smaller
bounded nilpotent family. The soluble cover is constructed unconditionally.
The relative tuple price uses the fixed rate 1/32 and is paid by the loss
in the smaller physical degree's quadratic term. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupNumericalClosure
open MarkedC4 CFSGOrdinarySubgroupUpperReduction
open CFSGSolubleWreathContainers CFSGSolublePrimitiveContainers

theorem exists_polylog_four_sqrt_constant :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 2 ≤ n →
      (Real.logb 2 ((n : ℝ) + 2)) ^ 4 ≤ D * Real.sqrt n := by
  let c : ℝ := 8 / Real.log 2
  refine ⟨2 * c ^ 4, by positivity, ?_⟩
  intro n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ Real.logb 2 ((n : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hL : Real.logb 2 ((n : ℝ) + 2) ≤
      c * ((n : ℝ) + 2) ^ (1 / 8 : ℝ) := by
    unfold Real.logb
    calc
      _ ≤ (((n : ℝ) + 2) ^ (1 / 8 : ℝ) / (1 / 8 : ℝ)) / Real.log 2 :=
        div_le_div_of_nonneg_right (Real.log_le_rpow_div hx (by norm_num)) hlog2.le
      _ = _ := by dsimp [c]; ring
  have ht : (((n : ℝ) + 2) ^ (1 / 8 : ℝ)) ^ (4 : ℕ) =
      Real.sqrt ((n : ℝ) + 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]
    norm_num
  have hs : Real.sqrt ((n : ℝ) + 2) ≤ 2 * Real.sqrt n := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt (Nat.cast_nonneg n)
    have h3 := Real.sqrt_nonneg ((n : ℝ) + 2)
    have h4 := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  calc
    _ ≤ (c * ((n : ℝ) + 2) ^ (1 / 8 : ℝ)) ^ 4 :=
      pow_le_pow_left₀ hL0 hL 4
    _ = c ^ 4 * Real.sqrt ((n : ℝ) + 2) := by rw [mul_pow, ht]
    _ ≤ c ^ 4 * (2 * Real.sqrt n) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem quadratic_loss (n m : ℝ) (hm : 0 ≤ m) (hmn : m ≤ n) :
    (n - m) ^ 2 / 16 + n * m / 16 ≤ n ^ 2 / 16 := by
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hmn)]

theorem relative_tuple_power_le (n m : ℕ) :
    ((((2 ^ (2 * n)) ^ (⌈(1 / 32 : ℝ) * m⌉₊) : ℕ)) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * m / 16 + 2 * n) := by
  have hc : (⌈(1 / 32 : ℝ) * m⌉₊ : ℝ) ≤ (1 / 32 : ℝ) * m + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  rw [← pow_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  have h := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 2 * n)
  nlinarith

theorem small_degree_log_error_le (A D : ℝ) (hA : 0 ≤ A)
    (n q : ℕ) (hqn : q ≤ n)
    (hD : (Real.logb 2 ((n : ℝ) + 2)) ^ 4 ≤ D * Real.sqrt n) :
    A * q * Real.logb 2 ((q : ℝ) + 2) ≤ A * D * n * Real.sqrt n := by
  have hqR : (q : ℝ) ≤ n := by exact_mod_cast hqn
  have hLq : 0 ≤ Real.logb 2 ((q : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num)
      (by have hq0 := (Nat.cast_nonneg q : (0 : ℝ) ≤ q); linarith)
  have hL : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    simp only [Real.rpow_one]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hmono : Real.logb 2 ((q : ℝ) + 2) ≤ Real.logb 2 ((n : ℝ) + 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hp : Real.logb 2 ((n : ℝ) + 2) ≤
      (Real.logb 2 ((n : ℝ) + 2)) ^ 4 := le_self_pow₀ hL (by decide)
  have hprod : (q : ℝ) * Real.logb 2 ((q : ℝ) + 2) ≤
      (n : ℝ) * (D * Real.sqrt n) :=
    (mul_le_mul hqR hmono hLq (Nat.cast_nonneg n)).trans
      (mul_le_mul_of_nonneg_left (hp.trans hD) (Nat.cast_nonneg n))
  calc
    _ = A * ((q : ℝ) * Real.logb 2 ((q : ℝ) + 2)) := by ring
    _ ≤ A * ((n : ℝ) * (D * Real.sqrt n)) := mul_le_mul_of_nonneg_left hprod hA
    _ = _ := by ring

theorem factorial_power_le (D : ℝ) (n : ℕ)
    (hD : (Real.logb 2 ((n : ℝ) + 2)) ^ 4 ≤ D * Real.sqrt n) :
    (n.factorial : ℝ) ≤ (2 : ℝ) ^ (3 * D * n * Real.sqrt n) := by
  have hL : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    simp only [Real.rpow_one]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hp : Real.logb 2 ((n : ℝ) + 2) ≤
      (Real.logb 2 ((n : ℝ) + 2)) ^ 4 := le_self_pow₀ hL (by decide)
  have hs : (logSize n : ℝ) ≤ 3 * D * Real.sqrt n := by
    have ht := logSize_add_one_real_le n
    push_cast at ht
    have h := mul_le_mul_of_nonneg_left (hp.trans hD) (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  calc
    _ ≤ (2 : ℝ) ^ ((n : ℝ) * logSize n) := by
      rw [← Nat.cast_mul, Real.rpow_natCast]
      exact_mod_cast factorial_le_two_pow n
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have h := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)
      nlinarith)

theorem convolution_term_le (C K n : ℕ) (hn : 2 ≤ n) (A D : ℝ) (hA : 0 ≤ A)
    (hD : (Real.logb 2 ((n : ℝ) + 2)) ^ 4 ≤ D * Real.sqrt n)
    (hnil : ∀ q : ℕ,
      (Nat.card (OrbitCutoffFamilies.NilpotentFamily C q) : ℝ) ≤
        (2 : ℝ) ^ ((q : ℝ) ^ 2 / 16 + A * q * Real.logb 2 ((q : ℝ) + 2)))
    (m : Fin (n + 1)) :
    ((2 ^ n * Nat.card (OrbitCutoffFamilies.NilpotentFamily C (n - m.val)) *
      (2 ^ (2 * n)) ^ (K * Nat.sqrt (2 * n) + ⌈(1 / 32 : ℝ) * m.val⌉₊) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + (A * D + 4 * K + 3) * n * Real.sqrt n) := by
  have hmn : m.val ≤ n := by omega
  have hmnR : (m.val : ℝ) ≤ n := by exact_mod_cast hmn
  have hq : ((n - m.val : ℕ) : ℝ) = (n : ℝ) - m.val := Nat.cast_sub hmn
  have hquad := quadratic_loss (n : ℝ) m.val (Nat.cast_nonneg _) hmnR
  have herr := small_degree_log_error_le A D hA n (n - m.val) (Nat.sub_le _ _) hD
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))
    simpa using h
  have hlinear : (3 : ℝ) * n ≤ 3 * n * Real.sqrt n := by
    exact le_mul_of_one_le_right (by positivity) hs
  have ht : (((2 ^ (2 * n)) ^
      (K * Nat.sqrt (2 * n) + ⌈(1 / 32 : ℝ) * m.val⌉₊) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (4 * (K : ℝ) * n * Real.sqrt n + (n : ℝ) * m.val / 16 + 2 * n) := by
    rw [pow_add, Nat.cast_mul]
    apply (mul_le_mul (container_tuple_power_le K n) (relative_tuple_power_le n m.val)
      (by positivity) (by positivity)).trans_eq
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have htwo : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ (n : ℝ) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
  calc
    _ = (2 : ℝ) ^ (n : ℝ) *
        (Nat.card (OrbitCutoffFamilies.NilpotentFamily C (n - m.val)) : ℝ) *
        (((2 ^ (2 * n)) ^
          (K * Nat.sqrt (2 * n) + ⌈(1 / 32 : ℝ) * m.val⌉₊) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, htwo]
    _ ≤ (2 : ℝ) ^ (n : ℝ) *
        (2 : ℝ) ^ (((n - m.val : ℕ) : ℝ) ^ 2 / 16 +
          A * ((n - m.val : ℕ) : ℝ) * Real.logb 2 (((n - m.val : ℕ) : ℝ) + 2)) *
        (2 : ℝ) ^ (4 * (K : ℝ) * n * Real.sqrt n + (n : ℝ) * m.val / 16 + 2 * n) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hnil _) (by positivity)) ht
        (by positivity) (by positivity)
    _ = (2 : ℝ) ^ ((n : ℝ) +
        (((n - m.val : ℕ) : ℝ) ^ 2 / 16 +
          A * ((n - m.val : ℕ) : ℝ) * Real.logb 2 (((n - m.val : ℕ) : ℝ) + 2)) +
        (4 * (K : ℝ) * n * Real.sqrt n + (n : ℝ) * m.val / 16 + 2 * n)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      rw [hq]
      rw [hq] at herr
      nlinarith)

theorem convolution_le (C K n : ℕ) (hn : 2 ≤ n) (A D : ℝ) (hA : 0 ≤ A)
    (hD : (Real.logb 2 ((n : ℝ) + 2)) ^ 4 ≤ D * Real.sqrt n)
    (hnil : ∀ q : ℕ,
      (Nat.card (OrbitCutoffFamilies.NilpotentFamily C q) : ℝ) ≤
        (2 : ℝ) ^ ((q : ℝ) ^ 2 / 16 + A * q * Real.logb 2 ((q : ℝ) + 2))) :
    ((∑ m : Fin (n + 1), 2 ^ n * Nat.card (OrbitCutoffFamilies.NilpotentFamily C (n - m.val)) *
      (2 ^ (2 * n)) ^ (K * Nat.sqrt (2 * n) + ⌈(1 / 32 : ℝ) * m.val⌉₊) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + (A * D + 4 * K + 4) * n * Real.sqrt n) := by
  let e : ℝ := (n : ℝ) ^ 2 / 16 + (A * D + 4 * K + 3) * n * Real.sqrt n
  have hlabel : ((n : ℝ) + 1) ≤ (2 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.succ_le_of_lt n.lt_two_pow_self
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))
    simpa using h
  have hlinear : (n : ℝ) ≤ n * Real.sqrt n :=
    le_mul_of_one_le_right (Nat.cast_nonneg n) hs
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _m : Fin (n + 1), (2 : ℝ) ^ e :=
      Finset.sum_le_sum (fun m _ => convolution_term_le C K n hn A D hA hD hnil m)
    _ = ((n : ℝ) + 1) * (2 : ℝ) ^ e := by simp
    _ ≤ (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ e :=
      mul_le_mul_of_nonneg_right hlabel (by positivity)
    _ = (2 : ℝ) ^ ((n : ℝ) + e) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp [e]; nlinarith)

/-- Internal final analytic implication. The bounded nilpotent estimate is
the independently proved smaller-family leaf, and is not an ordinary
all-subgroup count or a new public literature assumption. -/
theorem ordinary_upper_of_bounded_nilpotent
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (h62 : LargeOrbitOrdinaryGeneration.PublishedProposition62)
    (hbounded : ∀ C : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ q : ℕ,
      (Nat.card (OrbitCutoffFamilies.NilpotentFamily C q) : ℝ) ≤
        (2 : ℝ) ^ ((q : ℝ) ^ 2 / 16 + A * q * Real.logb 2 ((q : ℝ) + 2))) :
    OrdinarySubgroupUpper.PublishedTheoremOneUpper := by
  obtain ⟨C, _, hfinite⟩ :=
    CFSGOrdinaryBoundedNilpotentFormula.subgroup_card_le_bounded_nilpotent_convolution
      hAG h62 (1 / 32) (by norm_num)
  obtain ⟨A, hA, hnil⟩ := hbounded C
  obtain ⟨D, _, hD⟩ := exists_polylog_four_sqrt_constant
  let K := OrdinaryNilpotentGeneration.nilpotentControlCutoff C
  refine ⟨(4099 + A) * D + 4 * K + 4, ?_⟩
  intro n hn
  let E := CFSGSolubleFullContainerCover.cover n
  have hf := hfinite n E
  have hsum := convolution_le C K n hn A D hA (hD n hn) hnil
  have hfac := factorial_power_le D n (hD n hn)
  have hcover : (Nat.card E.Index : ℝ) ≤
      (2 : ℝ) ^ (4096 * D * n * Real.sqrt n) := by
    apply (cover_card_le_polylog n).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h := mul_le_mul_of_nonneg_left (hD n hn)
      (by positivity : (0 : ℝ) ≤ 4096 * n)
    nlinarith
  calc
    _ ≤ (n.factorial : ℝ) * (Nat.card E.Index : ℝ) *
        ((∑ m : Fin (n + 1), 2 ^ n *
          Nat.card (OrbitCutoffFamilies.NilpotentFamily C (n - m.val)) *
          (2 ^ (2 * n)) ^ (K * Nat.sqrt (2 * n) + ⌈(1 / 32 : ℝ) * m.val⌉₊) : ℕ) : ℝ) := by
      exact_mod_cast hf
    _ ≤ (2 : ℝ) ^ (3 * D * n * Real.sqrt n) *
        (2 : ℝ) ^ (4096 * D * n * Real.sqrt n) *
        (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + (A * D + 4 * K + 4) * n * Real.sqrt n) :=
      mul_le_mul (mul_le_mul hfac hcover (by positivity) (by positivity)) hsum
        (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupNumericalClosure
