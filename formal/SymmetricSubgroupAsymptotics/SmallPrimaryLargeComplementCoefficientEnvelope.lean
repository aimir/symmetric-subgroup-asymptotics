import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementArithmetic
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallExactMultiplicities

/-! A shared coefficient envelope for every positive binary affine
dimension. The coefficients are the literal SAME GL order and matching
valuation, including the translation head. The only scalar regimes are
whole primary/complement intervals; no fitted conclusion, top-degree
census, solvability or simple-generation assumption is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementCoefficientEnvelope
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity
open BinaryGeneralLinearSmallExactMultiplicities

def envelope (d q a : ℕ) (v L : ℝ) : ℝ :=
  ((matchingMultiplicity d q : ℝ)/v+
      ((totalMultiplicity d : ℝ)-(matchingMultiplicity d q : ℝ))/(q : ℝ)^a+
      1/((q : ℝ)^a*v))*Real.sqrt ((d : ℝ)+L)+Real.sqrt (1+(d : ℝ)/L)

private theorem log_le_of_le_pow (M k : ℕ) (hM : 0 < M) (hle : M ≤ 2^k) :
    Real.logb 2 (M : ℝ) ≤ (k : ℝ) := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast hM : (0 : ℝ) < M) (by exact_mod_cast hle : (M : ℝ) ≤ (2 : ℝ)^k)
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] using hh

theorem envelope_le (q a v d : ℕ) (hq : q.Prime) (hd : 1 ≤ d)
    (hv : 5 ≤ v) (hvM : v ≤ q^a) (hM64 : q^a < 64) (hcop : Nat.Coprime (q^a) v)
    (L : ℝ) (hL : 9/2 ≤ L)
    (hentropy : L ≤ Real.logb 2 ((q : ℝ)^a)+(3/2)*(v : ℝ)) :
    envelope d q a (v : ℝ) L ≤ (2 : ℝ)^d := by
  let M := q^a
  let C : ℝ := totalMultiplicity d
  let m : ℝ := matchingMultiplicity d q
  have hM7 : 7 ≤ M := SmallPrimaryLargeComplementArithmetic.primary_ge_seven q a v hq hv hvM hcop
  have hMpos : 0 < M := by omega
  have hM7R : (7 : ℝ) ≤ M := by exact_mod_cast hM7
  have hvR : (5 : ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith only [hvR]
  have hvMR : (v : ℝ) ≤ M := by exact_mod_cast hvM
  have hM0 : (0 : ℝ) < M := by linarith only [hM7R]
  have hv63 : (v : ℝ) ≤ 63 := by exact_mod_cast (show v ≤ 63 by omega)
  have hqpow : (q : ℝ)^a = (M : ℝ) := by simp only [M,Nat.cast_pow]
  have hlogM6 : Real.logb 2 (M : ℝ) ≤ 6 :=
    log_le_of_le_pow M 6 hMpos (by omega)
  have hL6 : L ≤ 6+(3/2)*(v : ℝ) := by
    rw [hqpow] at hentropy
    linarith only [hentropy,hlogM6]
  have hm0 : 0 ≤ m := by positivity
  have hmC : m ≤ C := by
    have hh := pair_factorizations_le_cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) q (q+1) (by omega)
    have hn : matchingMultiplicity d q ≤ totalMultiplicity d := by
      unfold matchingMultiplicity totalMultiplicity
      split_ifs <;> omega
    dsimp only [m,C]
    exact_mod_cast hn
  have hC0 : 0 ≤ C := by positivity
  have hCsq : C ≤ (d : ℝ)^2 := by
    dsimp only [C,totalMultiplicity]
    exact_mod_cast BinaryGeneralLinearTotalPrimeMultiplicity.dimension_add_GL_cardFactors_le_sq d
  have hjoint : m/(v : ℝ)+(C-m)/(M : ℝ)+1/((M : ℝ)*(v : ℝ)) ≤
      C/(v : ℝ)+1/(v : ℝ)^2 := by
    have hrest := div_le_div_of_nonneg_left (sub_nonneg.mpr hmC) hv0 hvMR
    have herr : 1/((M : ℝ)*(v : ℝ)) ≤ 1/(v : ℝ)^2 := by
      apply one_div_le_one_div_of_le (pow_pos hv0 2)
      nlinarith only [mul_le_mul_of_nonneg_right hvMR hv0.le]
    calc
      _ ≤ m/(v : ℝ)+(C-m)/(v : ℝ)+1/(v : ℝ)^2 :=
        add_le_add (add_le_add le_rfl hrest) herr
      _ = _ := by ring
  change (m/(v : ℝ)+(C-m)/(q : ℝ)^a+1/((q : ℝ)^a*(v : ℝ)))*
    Real.sqrt ((d : ℝ)+L)+Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d
  rw [hqpow]
  by_cases hd4 : 4 ≤ d
  · have hh := SmallPrimaryLargeComplementMargins.envelope_le (v : ℝ) d hvR hd4 C L hC0 hCsq
      (by linarith only [hL]) hL6
    exact (add_le_add (mul_le_mul_of_nonneg_right hjoint (Real.sqrt_nonneg _)) le_rfl).trans hh
  · have hcases : d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · have hC1 : C = 1 := by
        dsimp only [C]
        rw [totalMultiplicity_eq 1 (by decide)]
        norm_num [smallTotal]
      have hm1 : m ≤ 1 := by linarith only [hmC,hC1]
      have hh := SmallPrimaryLargeComplementOneMargin.envelope_le (M : ℝ) (v : ℝ) m C L
        hM7R hvR hvMR hm1 hC1.le hL hL6
      simpa only [Nat.cast_one,pow_one] using hh
    · have hC4 : C = 4 := by
        dsimp only [C]
        rw [totalMultiplicity_eq 2 (by decide)]
        norm_num [smallTotal]
      have hm3 : m ≤ 3 := by
        have hn := matchingMultiplicity_le_triangle 2 q
        norm_num at hn
        dsimp only [m]
        exact_mod_cast hn
      by_cases hM16 : 16 ≤ M
      · have hh := SmallPrimaryLargeComplementTwoMargins.large_primary_envelope_le
          (M : ℝ) (v : ℝ) m C L (by exact_mod_cast hM16) hvR hvMR hv63 hm3 hC4.le hL hL6
        simpa only [Nat.cast_ofNat,show (2 : ℝ)^2 = 4 by norm_num] using hh
      · have hM15 : M ≤ 15 := by omega
        by_cases hq2 : q = 2
        · subst q
          have hM8 : M = 8 := SmallPrimaryLargeComplementArithmetic.binary_short_eq_eight a hM7 (by omega)
          have hM8R : (M : ℝ) = 8 := by exact_mod_cast hM8
          have hlogM3 : Real.logb 2 (M : ℝ) ≤ 3 :=
            log_le_of_le_pow M 3 hMpos (by omega)
          have hL3 : L ≤ 3+(3/2)*(v : ℝ) := by
            rw [hqpow] at hentropy
            linarith only [hentropy,hlogM3]
          have hh := SmallPrimaryLargeComplementTwoMargins.binary_eight_envelope_le
            (v : ℝ) m C L hvR (by exact_mod_cast (show v ≤ 8 by omega)) hm3 hC4.le hL hL3
          simpa only [Nat.cast_ofNat,show (2 : ℝ)^2 = 4 by norm_num,hM8R] using hh
        · have hm1 : m ≤ 1 := by
            have hn : matchingMultiplicity 2 q ≤ 1 := by
              rw [matching_odd_eq 2 q (by decide) hq2]
              unfold smallOddMatching
              split_ifs <;> omega
            dsimp only [m]
            exact_mod_cast hn
          have hlogM4 : Real.logb 2 (M : ℝ) ≤ 4 :=
            log_le_of_le_pow M 4 hMpos (by omega)
          have hL4 : L ≤ 4+(3/2)*(v : ℝ) := by
            rw [hqpow] at hentropy
            linarith only [hentropy,hlogM4]
          have hh := SmallPrimaryLargeComplementArithmetic.odd_short_envelope_le
            (M : ℝ) (v : ℝ) m C L hM7R hvR hvMR
            (by exact_mod_cast (show v ≤ 15 by omega)) hm1 hC4.le hL hL4
          simpa only [Nat.cast_ofNat,show (2 : ℝ)^2 = 4 by norm_num] using hh
    · have hC8 : C = 8 := by
        dsimp only [C]
        rw [totalMultiplicity_eq 3 (by decide)]
        norm_num [smallTotal]
      have hh := SmallPrimaryLargeComplementThreeMargin.envelope_le (v : ℝ) C L
        hvR hC0 hC8.le hL hL6
      have hfirst := add_le_add (mul_le_mul_of_nonneg_right hjoint (Real.sqrt_nonneg (3+L)))
        (le_rfl : Real.sqrt (1+3/L) ≤ Real.sqrt (1+3/L))
      simpa only [Nat.cast_ofNat,show (2 : ℝ)^3 = 8 by norm_num] using hfirst.trans hh

end SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementCoefficientEnvelope
