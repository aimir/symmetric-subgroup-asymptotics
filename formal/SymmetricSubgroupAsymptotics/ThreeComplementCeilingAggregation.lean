import SymmetricSubgroupAsymptotics.BinaryAffineThreeComplementOneEnvelope
import SymmetricSubgroupAsymptotics.CentralBinomialNormalizedAntitone
import SymmetricSubgroupAsymptotics.OddSmallComplementCeilingAggregation

/-! The natural top ceiling for three times a binary primary degree.
All dimensions and exponents are covered except the two dimension-two
starting exponents, whose actual shared-head proof is separate. The
scope guard is purely arithmetic; no fitting inequality is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ThreeComplementCeilingAggregation
open ActualWreathChooseDivisorCapacity

private theorem log_three_bounds : (3/2 : ℝ) ≤ Real.logb 2 (3 : ℝ) ∧
    Real.logb 2 (3 : ℝ) ≤ 8/5 := by
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ)^3) (by norm_num : (2 : ℝ)^3 ≤ (3 : ℝ)^2)
  have hu := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (3 : ℝ)^5) (by norm_num : (3 : ℝ)^5 ≤ (2 : ℝ)^8)
  rw [Real.logb_pow,Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hl hu
  norm_num only [Nat.cast_ofNat] at hl hu
  exact ⟨by linarith only [hl],by linarith only [hu]⟩

private theorem rate_le_six (a : ℕ) (ha : 6 ≤ a) : primaryRate 2 a ≤ 5/16 := by
  have hh := CentralBinomialNormalizedAntitone.normalized_antitone ha
  have h6 : primaryRate 2 6 = 5/16 := by
    norm_num [primaryRate,show Nat.choose 6 3 = 20 by decide]
  have hle : primaryRate 2 a ≤ primaryRate 2 6 := by
    simpa only [primaryRate,show (2 : ℕ)-1 = 1 by decide,Nat.mul_one] using hh
  exact hle.trans_eq h6

private theorem rate_le_seven (a : ℕ) (ha : 7 ≤ a) : primaryRate 2 a ≤ 35/128 := by
  have hh := CentralBinomialNormalizedAntitone.normalized_antitone ha
  have h7 : primaryRate 2 7 = 35/128 := by
    norm_num [primaryRate,show Nat.choose 7 3 = 35 by decide]
  have hle : primaryRate 2 a ≤ primaryRate 2 7 := by
    simpa only [primaryRate,show (2 : ℕ)-1 = 1 by decide,Nat.mul_one] using hh
  exact hle.trans_eq h7

theorem aggregate_le (a d t : ℕ) (ha : 6 ≤ a) (hd : 1 ≤ d)
    (hregime : 3 ≤ d ∨ 8 ≤ a ∨ d = 1) (hshape : t = 3*2^a)
    (C m g : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2)
    (hcost : g ≤ (t : ℝ)*(m*primaryRate 2 a+(C-m)/(2 : ℝ)^a)+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  let B := Real.logb 2 (3 : ℝ)
  let M := (2 : ℝ)^a
  let u := primaryRate 2 a
  let b := m*u+(C-m)/M
  have ht0 : (0 : ℝ) < t := by
    have hh : 0 < t := by rw [hshape]; positivity
    exact_mod_cast hh
  have hM0 : 0 < M := by positivity
  have haR : (6 : ℝ) ≤ a := by exact_mod_cast ha
  have hB := log_three_bounds
  have hBlo : (3/2 : ℝ) ≤ B := hB.1
  have hBup : B ≤ 8/5 := hB.2
  have hB0 : 0 ≤ B := by linarith only [hBlo]
  have hshapeR : (t : ℝ) = 3*M := by dsimp only [M]; exact_mod_cast hshape
  have hlog : L = (a : ℝ)+B := by
    dsimp only [L]
    rw [hshapeR,Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0) hM0.ne']
    simp only [M,B,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
    ring
  have hL0 : 0 < L := by rw [hlog]; linarith only [haR,hB0]
  have hu0 : 0 ≤ u := by dsimp only [u,primaryRate]; positivity
  have hu6 : u ≤ 5/16 := rate_le_six a ha
  have hwall : u^2*(3*(a : ℝ)+2) ≤ 2 := by
    have hh := CentralBinomialSquareRootBound.normalized_square a
    have heq : (a.choose (a/2) : ℝ)/(2 : ℝ)^a = u := by
      simp only [u,primaryRate,show (2 : ℕ)-1 = 1 by decide,Nat.mul_one]
    rw [heq] at hh
    nlinarith only [hh]
  have hscaled : (m*u+(C-m+1/3)/M)*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
    by_cases hd3 : 3 ≤ d
    · exact BinaryAffineThreeComplementEnvelope.large_envelope_le a d ha hd3
        C m B u L hm0 hmC hC hmA hB0 hBup hu0 hu6 hwall
          (by rw [hlog]; linarith only [haR,hBlo]) hlog.le
    · by_cases hd1 : d = 1
      · subst d
        norm_num only [Nat.cast_one,pow_one] at hC hmA ⊢
        by_cases ha7 : 7 ≤ a
        · have ha7R : (7 : ℝ) ≤ a := by exact_mod_cast ha7
          exact BinaryAffineThreeComplementOneEnvelope.envelope_le a ha7 C m B u L
            hm0 hmC hC (by norm_num at hmA; exact hmA) hB0 hBup hu0
              (rate_le_seven a ha7) hwall (by rw [hlog]; linarith only [ha7R,hBlo]) hlog.le
        · have ha6 : a = 6 := by omega
          subst a
          apply BinaryAffineThreeComplementOneEnvelope.starting_envelope_le C m u L
            hm0 hmC hC (by norm_num at hmA; exact hmA) hu6
          · rw [hlog]
            norm_num only [Nat.cast_ofNat]
            linarith only [hBlo]
          · rw [hlog]
            norm_num only [Nat.cast_ofNat]
            linarith only [hBup]
      · have hd2 : 2 ≤ d := by omega
        have ha8 : 8 ≤ a := by rcases hregime with h | h | h <;> omega
        have ha8R : (8 : ℝ) ≤ a := by exact_mod_cast ha8
        exact BinaryAffineThreeComplementEnvelope.short_envelope_le a d ha8 hd2
          C m B u L hm0 hmC hC hmA hB0 hBup hu0 (rate_le_seven a (by omega)) hwall
            (by rw [hlog]; linarith only [ha8R,hBlo]) hlog.le
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(M*3) := by
    rw [hshapeR]
    field_simp [hM0.ne']
    exact le_rfl
  have hg : g ≤ (t : ℝ)*b+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M*3) := by
    change g ≤ (t : ℝ)*b+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hscaled' : (b+1/(M*3))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    have heq : b+1/(M*3) = m*u+(C-m+1/3)/M := by
      dsimp only [b]
      field_simp [hM0.ne'] <;> ring
    rw [heq]
    exact hscaled
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*b+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M*3))*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*((b+1/(M*3))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.ThreeComplementCeilingAggregation
