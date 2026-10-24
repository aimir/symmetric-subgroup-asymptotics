import SymmetricSubgroupAsymptotics.SmallPrimaryZeroMatchingMargins

/-! A dimension-uniform margin for a small dominant primary and a
complementary primary at least five. The SAME two-divisor estimate gives
a total rate C/v when v is no larger than the dominant primary. The
ceiling error remains 1/v^2, since the two coprime primary powers both
divide the actual degree. Polynomial doubling pays every dimension at
least four; this is not a table of top degrees or actions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementMargins

def budget (d : ℕ) : ℝ :=
  ((d : ℝ)^2+1/5)*((d : ℝ)+13)/20+1+(d : ℝ)/8

theorem budget_le (d : ℕ) (hd : 4 ≤ d) : budget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [budget]
  | succ d hd ih =>
      have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-4 := by linarith only [hdR]
      have heq : 2*budget d-budget (d+1) =
          ((d : ℝ)-4)^3/20+11*((d : ℝ)-4)^2/10+
            1017*((d : ℝ)-4)/200+1247/200 := by
        simp only [budget,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ ((d : ℝ)-4)^3/20+11*((d : ℝ)-4)^2/10+
          1017*((d : ℝ)-4)/200+1247/200 := by positivity
      have hstep : budget (d+1) ≤ 2*budget d := by linarith only [heq,hnonneg]
      calc
        budget (d+1) ≤ 2*budget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem root_div_le (v : ℝ) (d : ℕ) (hv : 5 ≤ v) (hd : 4 ≤ d) :
    Real.sqrt ((d : ℝ)+6+(3/2)*v)/v ≤ ((d : ℝ)+13)/20 := by
  have hv0 : 0 < v := by linarith only [hv]
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hprod : 0 ≤ (v-5)*(((d : ℝ)+6)*(v+5)+(15/2)*v) :=
    mul_nonneg (by linarith only [hv]) (by positivity)
  have hfrac : ((d : ℝ)+6+(3/2)*v)/v^2 ≤ ((d : ℝ)+27/2)/25 := by
    apply (div_le_iff₀ (pow_pos hv0 2)).mpr
    nlinarith only [hprod]
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg _) hv0.le) (by positivity)).mp
  rw [div_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (d : ℝ)+6+(3/2)*v)]
  have hlast : ((d : ℝ)+27/2)/25 ≤ (((d : ℝ)+13)/20)^2 := by
    have hh : 0 ≤ ((d : ℝ)-4)*((d : ℝ)+14) :=
      mul_nonneg (by linarith only [hdR]) (by positivity)
    nlinarith only [hh]
  exact hfrac.trans hlast

theorem envelope_le (v : ℝ) (d : ℕ) (hv : 5 ≤ v) (hd : 4 ≤ d)
    (C L : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ (d : ℝ)^2)
    (hL : 4 ≤ L) (hentropy : L ≤ 6+(3/2)*v) :
    (C/v+1/v^2)*Real.sqrt ((d : ℝ)+L)+Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
  have hv0 : 0 < v := by linarith only [hv]
  have hroot : Real.sqrt ((d : ℝ)+L)/v ≤ ((d : ℝ)+13)/20 :=
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
      (add_le_add (le_rfl : (d : ℝ) ≤ d) hentropy)) hv0.le).trans
        (by simpa only [add_assoc] using root_div_le v d hv hd)
  have hinv : 1/v ≤ (1/5 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hv
  have hmain : (C/v+1/v^2)*Real.sqrt ((d : ℝ)+L) ≤
      ((d : ℝ)^2+1/5)*((d : ℝ)+13)/20 := by
    have hcoef : C+1/v ≤ (d : ℝ)^2+1/5 := add_le_add hC hinv
    have hfirst := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ C+1/v by positivity)
    have hsecond := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ ((d : ℝ)+13)/20 by positivity)
    have hh := hfirst.trans hsecond
    convert hh using 1 <;> field_simp [hv0.ne'] <;> ring
  have htop : Real.sqrt (1+(d : ℝ)/L) ≤ 1+(d : ℝ)/8 := by
    have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
      (by norm_num : (0 : ℝ) < 4) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  calc
    (C/v+1/v^2)*Real.sqrt ((d : ℝ)+L)+Real.sqrt (1+(d : ℝ)/L) ≤ budget d := by
      dsimp only [budget]
      linarith only [hmain,htop]
    _ ≤ (2 : ℝ)^d := budget_le d hd

end SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementMargins
