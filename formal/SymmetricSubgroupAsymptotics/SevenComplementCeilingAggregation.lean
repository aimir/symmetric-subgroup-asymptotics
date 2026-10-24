import SymmetricSubgroupAsymptotics.BinaryAffineSevenComplementEnvelope
import SymmetricSubgroupAsymptotics.OddSmallComplementCeilingAggregation

/-! The exact natural top ceiling on the complementary interval [7,15].
Its error is charged to the actual product of the two coprime primary
powers, not merely to the binary power. No fitted scalar bound is an
input: the retained Wallis square is proved for the literal choose rate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SevenComplementCeilingAggregation
open ActualWreathChooseDivisorCapacity

theorem aggregate_le (a d t v : ℕ) (ha : 6 ≤ a) (hd1 : 1 ≤ d) (hd6 : d ≤ 6)
    (ht : 2 ≤ t) (hv : 7 ≤ v) (hMv : 2^a*v ≤ t)
    (C m B g : ℝ) (hm0 : 0 ≤ m) (hmC : m ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hmA : m ≤ (d : ℝ)*((d : ℝ)+1)/2)
    (hB0 : 0 ≤ B) (hB16 : B ≤ 16) (hBv : 7*B ≤ (v : ℝ)^2)
    (hL8 : 8 ≤ Real.logb 2 (t : ℝ))
    (hentropy : Real.logb 2 (t : ℝ) ≤ (a : ℝ)+B)
    (hcost : g ≤ (t : ℝ)*(m*min (primaryRate 2 a) (1/(v : ℝ))+
      (C-m)/(2 : ℝ)^a)+(⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  let M := (2 : ℝ)^a
  let u := primaryRate 2 a
  let r := min u (1/(v : ℝ))
  let b := m*r+(C-m)/M
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hvR : (7 : ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  have hM0 : 0 < M := by positivity
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL8]
  have hu0 : 0 ≤ u := by dsimp only [u,primaryRate]; positivity
  have hr0 : 0 ≤ r := le_min hu0 (div_nonneg (by norm_num) hv0.le)
  have hru : r ≤ u := min_le_left _ _
  have hr2 : r^2 ≤ u^2 := (sq_le_sq₀ hr0 hu0).mpr hru
  have huwall : (3*(a : ℝ)+2)*u^2 ≤ 2 := by
    simpa only [u,primaryRate,show (2 : ℕ)-1 = 1 by decide,Nat.mul_one] using
      CentralBinomialSquareRootBound.normalized_square a
  have hwall : r^2*(3*(a : ℝ)+2) ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hr2
      (show 0 ≤ 3*(a : ℝ)+2 by positivity)
    nlinarith only [hh,huwall]
  have hcap : r*(v : ℝ) ≤ 1 :=
    (le_div_iff₀ hv0).mp (min_le_right u (1/(v : ℝ)))
  have hscaled := BinaryAffineSevenComplementEnvelope.envelope_le a d ha hd1 hd6
    C m B (v : ℝ) r L hm0 hmC hC hmA hB0 hB16 hBv hvR hr0 hwall hcap hL8 hentropy
  have hratio : Real.sqrt ((d : ℝ)+L)/Real.sqrt L = Real.sqrt (1+(d : ℝ)/L) := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ (d : ℝ)+L)]
    congr 1
    field_simp [hL0.ne'] <;> ring
  have hceil : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (t : ℝ)/Real.sqrt L+1 :=
    (Nat.ceil_lt_add_one (div_nonneg ht0.le (Real.sqrt_nonneg _))).le
  have hMvR : M*(v : ℝ) ≤ t := by dsimp only [M]; exact_mod_cast hMv
  have hunit : (1 : ℝ) ≤ (t : ℝ)/(M*(v : ℝ)) :=
    (le_div_iff₀ (mul_pos hM0 hv0)).mpr (by simpa only [one_mul] using hMvR)
  have hg : g ≤ (t : ℝ)*b+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M*(v : ℝ)) := by
    change g ≤ (t : ℝ)*b+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hcost
    linarith only [hcost,hceil,hunit]
  have hs : 0 < Real.sqrt ((d : ℝ)+L) := Real.sqrt_pos.mpr (by positivity)
  have hscaled' : (b+1/(M*(v : ℝ)))*Real.sqrt ((d : ℝ)+L)+
      Real.sqrt ((d : ℝ)+L)/Real.sqrt L ≤ (2 : ℝ)^d := by
    rw [hratio]
    have heq : b+1/(M*(v : ℝ)) = m*r+(C-m+1/(v : ℝ))/M := by
      dsimp only [b]
      field_simp [hM0.ne',hv0.ne'] <;> ring
    rw [heq]
    exact hscaled
  change g ≤ (2 : ℝ)^d*(t : ℝ)/Real.sqrt ((d : ℝ)+L)
  apply (le_div_iff₀ hs).mpr
  calc
    g*Real.sqrt ((d : ℝ)+L) ≤
        ((t : ℝ)*b+(t : ℝ)/Real.sqrt L+(t : ℝ)/(M*(v : ℝ)))*
          Real.sqrt ((d : ℝ)+L) := mul_le_mul_of_nonneg_right hg hs.le
    _ = (t : ℝ)*((b+1/(M*(v : ℝ)))*Real.sqrt ((d : ℝ)+L)+
        Real.sqrt ((d : ℝ)+L)/Real.sqrt L) := by ring
    _ ≤ (t : ℝ)*(2 : ℝ)^d := mul_le_mul_of_nonneg_left hscaled' ht0.le
    _ = (2 : ℝ)^d*(t : ℝ) := mul_comm _ _

end SymmetricSubgroupAsymptotics.SevenComplementCeilingAggregation
