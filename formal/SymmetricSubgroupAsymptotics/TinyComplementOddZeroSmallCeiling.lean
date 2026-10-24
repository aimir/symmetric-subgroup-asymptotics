import SymmetricSubgroupAsymptotics.TinyComplementOddZeroSmallMargins
import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput

/-! Ceiling normalization of the lower-dimensional zero-matching
intervals. A nonpure top has at least twice its actual primary divisor,
so its literal rounding term is at most half a primary unit. All log
bounds follow from the stated integer degree intervals. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyComplementOddZeroSmallCeiling

theorem aggregate_le (M d t : ℕ) (hM : 5 ≤ M) (hMt : 2*M ≤ t)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (ht128 : t ≤ 128) (hsmall : d = 1 ∨ t ≤ 64)
    (C g : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ if d = 1 then 1 else (2 : ℝ)^d)
    (hcost : g ≤ (t : ℝ)*C/(M : ℝ)+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have ht10 : 10 ≤ t := by omega
  have hMR : (5 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith only [hMR]
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hMtR : (2 : ℝ)*(M : ℝ) ≤ t := by exact_mod_cast hMt
  have hL3 : 3 ≤ L := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 3
      (by omega) (by decide) (by simpa only [pow_one] using (show 2^3 ≤ t by omega))
    simpa only [L,Nat.cast_one,Nat.cast_ofNat,div_one] using hh
  have hL7 : L ≤ 7 := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 7
      (by omega) (by decide) (by simpa only [pow_one] using ht128)
    simpa only [L,Nat.cast_one,Nat.cast_ofNat,div_one] using hh
  have hL13 : (13/4 : ℝ) ≤ L := by
    have hp := Nat.pow_le_pow_left ht10 4
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 4 13
      (by omega) (by decide) ((by decide : 2^13 ≤ 10^4).trans hp)
    simpa only [L,Nat.cast_ofNat] using hh
  have hscaled : ((C+1/2)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
    rcases hd with hdEq | hdEq | hdEq
    · have hC1 : C ≤ 1 := by simpa only [hdEq,if_pos rfl] using hC
      have hh := TinyComplementOddZeroSmallMargins.one_nonpure_envelope_le
        (M : ℝ) C L hMR hC0 hC1 hL13 hL7
      simpa only [hdEq,Nat.cast_one,pow_one] using hh
    · have ht64 : t ≤ 64 := hsmall.resolve_left (by omega)
      have hL6 : L ≤ 6 := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 6
          (by omega) (by decide) (by simpa only [pow_one] using ht64)
        simpa only [L,Nat.cast_one,Nat.cast_ofNat,div_one] using hh
      have hC4 : C ≤ 4 := by
        simpa only [hdEq,show (2 : ℕ) ≠ 1 by decide,if_false,
          show (2 : ℝ)^2 = 4 by norm_num] using hC
      have hh := TinyComplementOddZeroSmallMargins.two_five_nonpure_envelope_le
        (M : ℝ) C L hMR hC0 hC4 hL3 hL6
      simpa only [hdEq,Nat.cast_ofNat,show (2 : ℝ)^2 = 4 by norm_num] using hh
    · have ht64 : t ≤ 64 := hsmall.resolve_left (by omega)
      have hL6 : L ≤ 6 := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 6
          (by omega) (by decide) (by simpa only [pow_one] using ht64)
        simpa only [L,Nat.cast_one,Nat.cast_ofNat,div_one] using hh
      have hC8 : C ≤ 8 := by
        simpa only [hdEq,show (3 : ℕ) ≠ 1 by decide,if_false,
          show (2 : ℝ)^3 = 8 by norm_num] using hC
      have hh := TinyComplementOddZeroSmallMargins.three_five_envelope_le
        (M : ℝ) C L hMR hC0 hC8 (by linarith only [hL3]) hL6
      have hrate : (C+1/2)/(M : ℝ) ≤ (C+1)/(M : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hM0.le
      have hmain := mul_le_mul_of_nonneg_right hrate (Real.sqrt_nonneg (3+L))
      have hlast := (add_le_add hmain (le_rfl : Real.sqrt (1+3/L) ≤ Real.sqrt (1+3/L))).trans hh
      simpa only [hdEq,Nat.cast_ofNat,show (2 : ℝ)^3 = 8 by norm_num] using hlast
  have hL0 : 0 < L := by linarith only [hL3]
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg htR.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(2*(M : ℝ)) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(M : ℝ))).mpr
      (by simpa only [one_mul] using hMtR)
  have hg : g ≤ (t : ℝ)*C/(M : ℝ)+(t : ℝ)/Real.sqrt L+(t : ℝ)/(2*(M : ℝ)) := by
    change g ≤ (t : ℝ)*C/(M : ℝ)+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hscaled' : ((C+1/2)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    exact hscaled
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*C/(M : ℝ)+(t : ℝ)/Real.sqrt L+(t : ℝ)/(2*(M : ℝ)))*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*(((C+1/2)/(M : ℝ))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by
      field_simp [hM0.ne',(Real.sqrt_pos.mpr hL0).ne'] <;> ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' htR.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.TinyComplementOddZeroSmallCeiling
