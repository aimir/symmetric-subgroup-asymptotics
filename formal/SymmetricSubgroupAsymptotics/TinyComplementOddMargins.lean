import SymmetricSubgroupAsymptotics.SmallPrimaryLargeComplementMargins

/-! A universal small-complement odd-primary margin. The matching and
remaining costs belong to the SAME order and are optimized together.
The exact small GL coefficients can supply C<=d^2-2 and m<=d-2; the
scalar theorem itself uses polynomial doubling in every d>=4. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TinyComplementOddMargins

theorem joint_rate_le (M N m C A B u : ℝ) (hN : 2 ≤ N) (hM : N ≤ M)
    (hm0 : 0 ≤ m) (hmA : m ≤ A) (hmC : m ≤ C) (hC : C ≤ B) (hu : u ≤ 1/2) :
    m*u+(C-m+1)/M ≤ A/2+(B-A+1)/N := by
  have hN0 : 0 < N := by linarith only [hN]
  have hrest0 : 0 ≤ C-m+1 := by linarith only [hmC]
  have hfirst : m*u ≤ m/2 := by
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hu hm0
  have hrest := div_le_div_of_nonneg_left hrest0 hN0 hM
  have hslope0 : 0 ≤ (1/2 : ℝ)-1/N :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hN)
  have hslope := mul_le_mul_of_nonneg_right hmA hslope0
  have hlast := div_le_div_of_nonneg_right (add_le_add hC (le_rfl : (1 : ℝ) ≤ 1)) hN0.le
  calc
    m*u+(C-m+1)/M ≤ m/2+(C-m+1)/N := add_le_add hfirst hrest
    _ = m*((1/2)-1/N)+(C+1)/N := by ring
    _ ≤ A*((1/2)-1/N)+(B+1)/N := add_le_add hslope hlast
    _ = A/2+(B-A+1)/N := by ring

def budget (d : ℕ) : ℝ :=
  ((d : ℝ)^2/5+3*(d : ℝ)/10-4/5)*((d : ℝ)+11)/4+1+(d : ℝ)/4

theorem budget_le (d : ℕ) (hd : 4 ≤ d) : budget d ≤ (2 : ℝ)^d := by
  induction d,hd using Nat.le_induction with
  | base => norm_num [budget]
  | succ d hd ih =>
      have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
      have hx : 0 ≤ (d : ℝ)-4 := by linarith only [hdR]
      have heq : 2*budget d-budget (d+1) =
          ((d : ℝ)-4)^3/20+43*((d : ℝ)-4)^2/40+
            227*((d : ℝ)-4)/40+119/20 := by
        simp only [budget,Nat.cast_add,Nat.cast_one]
        ring
      have hnonneg : 0 ≤ ((d : ℝ)-4)^3/20+43*((d : ℝ)-4)^2/40+
          227*((d : ℝ)-4)/40+119/20 := by positivity
      have hstep : budget (d+1) ≤ 2*budget d := by linarith only [heq,hnonneg]
      calc
        budget (d+1) ≤ 2*budget d := hstep
        _ ≤ 2*(2 : ℝ)^d := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ)^(d+1) := by rw [pow_succ]; ring

theorem higher_envelope_le (d : ℕ) (hd : 4 ≤ d) (M m C u L : ℝ)
    (hM : 5 ≤ M) (hm0 : 0 ≤ m) (hmA : m ≤ (d : ℝ)-2) (hmC : m ≤ C)
    (hC : C ≤ (d : ℝ)^2-2) (hu : u ≤ 1/2) (hL : 2 ≤ L) (hL10 : L ≤ 10) :
    (m*u+(C-m+1)/M)*Real.sqrt ((d : ℝ)+L)+Real.sqrt (1+(d : ℝ)/L) ≤ (2 : ℝ)^d := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hrate : m*u+(C-m+1)/M ≤ (d : ℝ)^2/5+3*(d : ℝ)/10-4/5 := by
    have hh := joint_rate_le M 5 m C ((d : ℝ)-2) ((d : ℝ)^2-2) u
      (by norm_num) hM hm0 hmA hmC hC hu
    convert hh using 1 <;> ring
  have hcoef : 0 ≤ (d : ℝ)^2/5+3*(d : ℝ)/10-4/5 := by
    nlinarith only [sq_nonneg (d : ℝ),hdR]
  have hroot : Real.sqrt ((d : ℝ)+L) ≤ ((d : ℝ)+11)/4 := by
    have hprod : 0 ≤ ((d : ℝ)-4)*((d : ℝ)+10) :=
      mul_nonneg (by linarith only [hdR]) (by positivity)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hprod,hL10]
  have hmain := mul_le_mul hrate hroot (Real.sqrt_nonneg _) hcoef
  have htop : Real.sqrt (1+(d : ℝ)/L) ≤ 1+(d : ℝ)/4 := by
    have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ d by positivity)
      (by norm_num : (0 : ℝ) < 2) hL
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [sq_nonneg (d : ℝ)]
  calc
    (m*u+(C-m+1)/M)*Real.sqrt ((d : ℝ)+L)+Real.sqrt (1+(d : ℝ)/L) ≤ budget d := by
      dsimp only [budget]
      linarith only [hmain,htop]
    _ ≤ (2 : ℝ)^d := budget_le d hd

end SymmetricSubgroupAsymptotics.TinyComplementOddMargins
