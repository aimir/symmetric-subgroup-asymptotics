import SymmetricSubgroupAsymptotics.C1LowCone
import SymmetricSubgroupAsymptotics.FusionArbitraryWidth

/-! Numerical c=1 earlier-owner rows, with every polynomial and original
divisor retained. These prove the complete numerical step for the listed
exponents; concrete local epimorphism bounds and actual ownership remain
separate group-theoretic obligations, not assumptions hidden in this file. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter
namespace SymmetricSubgroupAsymptotics

inductive C1EarlierRow
  | degreeSix | degreeTwelve | degreeTwelveMixed | degreeNine | degreeTwentySeven
  deriving DecidableEq, Fintype

def c1EarlierWidth : C1EarlierRow → ℕ
  | .degreeSix => 6
  | .degreeTwelve => 12
  | .degreeTwelveMixed => 12
  | .degreeNine => 9
  | .degreeTwentySeven => 27

/-- Rational envelopes obtained uniformly from log₂3 < 8/5. -/
def c1EarlierExponent : C1EarlierRow → ℝ
  | .degreeSix => 8/15
  | .degreeTwelve => 16/15
  | .degreeTwelveMixed => 25/18
  | .degreeNine => 8/9
  | .degreeTwentySeven => 8/3

theorem c1EarlierWidth_pos (r : C1EarlierRow) : 0<c1EarlierWidth r := by
  cases r <;> decide

/-- Even the weakest conditional rows have a uniform 1/9 margin.
For odd widths the floor(w/2) loss, not w/8, is used. -/
theorem c1EarlierExponent_gap (r : C1EarlierRow) :
    (1:ℝ)/9 ≤ (halfDegree (c1EarlierWidth r):ℝ)/4-c1EarlierExponent r := by
  cases r <;> norm_num [c1EarlierWidth,c1EarlierExponent,halfDegree]

theorem c1_ternary_rpow_envelope {x : ℝ} (hx : 0≤x) :
    (3:ℝ)^x ≤ (2:ℝ)^(((8:ℝ)/5)*x) := by
  calc
    _ ≤ ((2:ℝ)^((8:ℝ)/5))^x :=
      Real.rpow_le_rpow (by norm_num) c1_three_le_binary_envelope hx
    _ = _ := (Real.rpow_mul (by norm_num) _ _).symm

/-- The polynomial factor from the full fixed-target normal menu remains
inside the kernel until exponential decay is proved. -/
def c1EarlierKernel (b : ℕ) (r : C1EarlierRow) (D a : ℝ) : ℝ :=
  ((b:ℝ)+1)*fusionWidthColdKernel b (c1EarlierWidth r) D a (c1EarlierExponent r)

theorem c1EarlierKernel_nonneg (b : ℕ) (r : C1EarlierRow) {D a : ℝ}
    (hD : 0≤D) (ha : 0<a) : 0≤c1EarlierKernel b r D a :=
  mul_nonneg (by positivity) (fusionWidthColdKernel_nonneg _ _ hD ha)

/-- Every earlier numerical row decays at a single rational rate, in
both ambient parities, before any bound on s_b/L_b is used. -/
theorem c1EarlierKernel_eventually (r : C1EarlierRow) {D a : ℝ}
    (hD : 0≤D) (ha : 0<a) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ b : ℕ in atTop,
      c1EarlierKernel b r D a ≤ C*(2:ℝ)^(-(1/36:ℝ)*b) := by
  have hg := c1EarlierExponent_gap r
  have hgap : c1EarlierExponent r < (halfDegree (c1EarlierWidth r):ℝ)/4 := by linarith
  obtain ⟨C,hC,hb⟩ := fusionWidthColdKernel_eventually (c1EarlierWidth r) hD ha hgap
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hb,eventually_shifted_natpow_mul_exponential_le 1 1
    (show (0:ℝ)<1/18 by norm_num)] with b hb hp
  have hm : -(((halfDegree (c1EarlierWidth r):ℝ)/4-c1EarlierExponent r)/2)*b ≤
      -(1/18:ℝ)*b := by
    nlinarith [mul_nonneg (show (0:ℝ)≤b by positivity) (show
      (0:ℝ)≤(halfDegree (c1EarlierWidth r):ℝ)/4-c1EarlierExponent r-1/9 by linarith)]
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hm
  have hp' : ((b:ℝ)+1)*(2:ℝ)^(-(1/18:ℝ)*b) ≤ 2*(2:ℝ)^(-(1/36:ℝ)*b) := by
    norm_num only [pow_one,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hp
    convert hp using 1
  calc
    _ ≤ ((b:ℝ)+1)*(C*(2:ℝ)^(-(((halfDegree (c1EarlierWidth r):ℝ)/4-c1EarlierExponent r)/2)*b)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ((b:ℝ)+1)*(C*(2:ℝ)^(-(1/18:ℝ)*b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC.le) (by positivity)
    _ = C*(((b:ℝ)+1)*(2:ℝ)^(-(1/18:ℝ)*b)) := by ring
    _ ≤ C*(2*(2:ℝ)^(-(1/36:ℝ)*b)) := mul_le_mul_of_nonneg_left hp' hC.le
    _ = _ := by ring

/-- Any fixed finite original action menu made from these rows has an
exponentially vanishing aggregate at the actual complement n-w. -/
theorem c1EarlierKernel_shifted_sum {ι : Type*} [Fintype ι]
    (r : ι → C1EarlierRow) (D a : ι → ℝ)
    (hD : ∀ i,0≤D i) (ha : ∀ i,0<a i) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      (∑ i, c1EarlierKernel (n-c1EarlierWidth (r i)) (r i) (D i) (a i)) ≤
        C*(2:ℝ)^(-κ*(n:ℝ)) := by
  have h := fusion_finite_shifted_decay
    (fun i b => c1EarlierKernel b (r i) (D i) (a i))
    (fun i => c1EarlierWidth (r i)) 1 (fun i => ?_)
  · simpa only [pow_one] using h
  · obtain ⟨C,hC,hb⟩ := c1EarlierKernel_eventually (r i) (hD i) (ha i)
    exact ⟨C,1/36,hC,by norm_num,by simpa using hb⟩

end SymmetricSubgroupAsymptotics
