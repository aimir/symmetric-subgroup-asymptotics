import SymmetricSubgroupAsymptotics.BinaryAffineFiveComplementEnvelope
import SymmetricSubgroupAsymptotics.OddSmallComplementCeilingAggregation

/-! The exact top ceiling is charged through the actual divisor
5*2^a. The same correlated chief coefficients enter the uniform
five-complement envelope; no local dimension cutoff is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiveComplementCeilingAggregation
open ActualWreathChooseDivisorCapacity

theorem aggregate_le (a d t : ℕ) (ha : 6 ≤ a) (hd : 1 ≤ d) (ht : 2 ≤ t)
    (hMt : 2^a*5 ≤ t) (C m B g : ℝ)
    (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2) (hB0 : 0 ≤ B) (hB4 : B ≤ 4)
    (hL : 33/4 ≤ Real.logb 2 (t : ℝ))
    (hentropy : Real.logb 2 (t : ℝ) ≤ (a : ℝ)+B)
    (hcost : g ≤ (t : ℝ)*(m*min (primaryRate 2 a) (1/5)+
      (C-m)/(2 : ℝ)^a)+(⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  let M := (2 : ℝ)^a
  let u := primaryRate 2 a
  let r := min u (1/5)
  let b := m*r+(C-m)/M
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hM0 : 0 < M := by positivity
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL]
  have hu0 : 0 ≤ u := by dsimp only [u,primaryRate]; positivity
  have hr0 : 0 ≤ r := le_min hu0 (by norm_num)
  have hr2 : r^2 ≤ u^2 := (sq_le_sq₀ hr0 hu0).mpr (min_le_left _ _)
  have huwall : (3*(a : ℝ)+2)*u^2 ≤ 2 := by
    simpa only [u,primaryRate,show (2 : ℕ)-1 = 1 by decide,Nat.mul_one] using
      CentralBinomialSquareRootBound.normalized_square a
  have hwall : r^2*(3*(a : ℝ)+2) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hr2
      (show 0 ≤ 3*(a : ℝ)+2 by positivity)
    nlinarith only [hh,huwall]
  have hcap : 5*r ≤ 1 := by have hh := min_le_right u (1/5 : ℝ); linarith only [hh]
  have hscaled := BinaryAffineFiveComplementEnvelope.envelope_le a d ha hd
    C m B r L hm0 hmC hC hmA hB0 hB4 hr0 hwall hcap hL hentropy
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hMtR : M*5 ≤ t := by dsimp only [M]; exact_mod_cast hMt
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(M*5) :=
    (le_div_iff₀ (by positivity : 0 < M*5)).mpr (by simpa only [one_mul] using hMtR)
  have hg : g ≤ (t : ℝ)*b+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M*5) := by
    change g ≤ (t : ℝ)*b+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hscaled' : (b+1/(M*5))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    have heq : b+1/(M*5) = m*r+(C-m+1/5)/M := by
      dsimp only [b]
      field_simp [hM0.ne'] <;> ring
    rw [heq]
    exact hscaled
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*b+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M*5))*Real.sqrt ((d : ℝ)+L) :=
      mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*((b+1/(M*5))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.FiveComplementCeilingAggregation
