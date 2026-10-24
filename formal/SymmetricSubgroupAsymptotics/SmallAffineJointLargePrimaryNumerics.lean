import SymmetricSubgroupAsymptotics.CoarseTopCeilingRelativeError

/-! Three literal local-order multiplicity budgets share one interval
argument. These are scalar bounds for orders20,42,432, not a census of
actions. Both estimates refer to the same cost; the actual top ceiling
is retained, including its integer error. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallAffineJointLargePrimaryNumerics

private theorem interval_coefficient (H b s L R K B : ℝ)
    (hH : 0 ≤ H) (hb : 0 ≤ b) (hs : 0 ≤ s) (hL : 0 < L)
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hroot : L ≤ R^2)
    (hratio : s+L ≤ K^2*L) (hnum : (H*R+b)*K ≤ B) :
    (H+b/Real.sqrt L)*Real.sqrt (s+L) ≤ B := by
  have hrootPos := Real.sqrt_pos.mpr hL
  have hrootR : Real.sqrt L ≤ R := (Real.sqrt_le_iff).mpr ⟨hR,hroot⟩
  have hratioRoot : Real.sqrt (s+L) ≤ K*Real.sqrt L := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hK hrootPos.le)).mp
    rw [Real.sq_sqrt (by linarith only [hs,hL]),mul_pow,Real.sq_sqrt hL.le]
    exact hratio
  calc
    (H+b/Real.sqrt L)*Real.sqrt (s+L) ≤ (H+b/Real.sqrt L)*(K*Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hratioRoot (by positivity)
    _ = (H*Real.sqrt L+b)*K := by field_simp [hrootPos.ne'] <;> ring
    _ ≤ (H*R+b)*K := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hrootR hH) le_rfl) hK
    _ ≤ B := hnum

private theorem aggregate (t : ℕ) (ht : 8 ≤ t)
    (R H B S K₁ K₂ s g : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hs0 : 0 ≤ s) (hs : s ≤ S)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hsmall : (H+3/4)^2*(S+4) ≤ R^2)
    (hratio₁ : S+4 ≤ K₁^2*4) (hratio₂ : S+6 ≤ K₂^2*6)
    (hnum₁ : (H*(5/2)+9/8)*K₁ ≤ R)
    (hnum₂ : (H*(16/5)+9/8)*K₂ ≤ R)
    (hlarge : (B+9/8)^2*(S+10) ≤ R^2*10)
    (hhalf : g ≤ H*(t : ℝ)+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ))
    (hlog : g ≤ B*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ R*(t : ℝ)/Real.sqrt (s+Real.logb 2 (t : ℝ)) := by
  let L := Real.logb 2 (t : ℝ)
  have htR : (8 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hL3 : 3 ≤ L := by
    have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 3 (by omega)
      (by decide) (by simpa only [pow_one] using ht)
    simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hh
  have hL : 0 < L := by linarith only [hL3]
  have hrootL := Real.sqrt_pos.mpr hL
  have hrootS := Real.sqrt_pos.mpr (show 0 < s+L by linarith only [hs0,hL])
  change g ≤ H*(t : ℝ)+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hhalf
  change g ≤ B*(t : ℝ)/Real.sqrt L+(⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) at hlog
  change g ≤ R*(t : ℝ)/Real.sqrt (s+L)
  by_cases h16 : t ≤ 16
  · have hL4 : L ≤ 4 := by
      have hh := IntegerLogSquareRootCeilingCertificate.log_upper t 1 4 (by omega)
        (by decide) (by simpa only [pow_one] using h16)
      simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hh
    have hrootLower : (5/3 : ℝ) ≤ Real.sqrt L := by
      nlinarith only [Real.sq_sqrt hL.le,Real.sqrt_nonneg L,hL3]
    have hdiv : (t : ℝ)/Real.sqrt L ≤ (3/5)*(t : ℝ) := by
      apply (div_le_iff₀ hrootL).mpr
      have hh := mul_le_mul_of_nonneg_left hrootLower ht0
      nlinarith only [hh]
    have hceil := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (t : ℝ)/Real.sqrt L by positivity)).le
    have hceil' : (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (3/4)*(t : ℝ) := by
      linarith only [hceil,hdiv,htR]
    have hg : g ≤ (H+3/4)*(t : ℝ) := by linarith only [hhalf,hceil']
    have hcoef : (H+3/4)*Real.sqrt (s+L) ≤ R := by
      apply (sq_le_sq₀ (by positivity) hR).mp
      rw [mul_pow,Real.sq_sqrt (by linarith only [hs0,hL])]
      have hh := mul_le_mul_of_nonneg_left
        (show s+L ≤ S+4 by linarith only [hs,hL4]) (sq_nonneg (H+3/4))
      exact hh.trans hsmall
    apply (le_div_iff₀ hrootS).mpr
    calc
      g*Real.sqrt (s+L) ≤ ((H+3/4)*(t : ℝ))*Real.sqrt (s+L) :=
        mul_le_mul_of_nonneg_right hg hrootS.le
      _ = ((H+3/4)*Real.sqrt (s+L))*(t : ℝ) := by ring
      _ ≤ R*(t : ℝ) := mul_le_mul_of_nonneg_right hcoef ht0
  · have ht16 : 16 ≤ t := by omega
    have hL4 : 4 ≤ L := by
      have hh := IntegerLogSquareRootCeilingCertificate.log_lower t 1 4 (by omega)
        (by decide) (by simpa only [pow_one] using ht16)
      simpa only [Nat.cast_ofNat,Nat.cast_one,div_one] using hh
    have hceil := CoarseTopCeilingRelativeError.ceil_le_nine_eighths t ht16
    change (⌈(t : ℝ)/Real.sqrt L⌉₊ : ℝ) ≤ (9/8)*((t : ℝ)/Real.sqrt L) at hceil
    by_cases h10 : L ≤ 10
    · have hcoef : (H+(9/8)/Real.sqrt L)*Real.sqrt (s+L) ≤ R := by
        by_cases h6 : L ≤ 6
        · exact interval_coefficient H (9/8) s L (5/2) K₁ R hH (by norm_num)
            hs0 hL (by norm_num) hK₁ (by nlinarith only [h6])
            (by
              have hK : 0 ≤ K₁^2-1 := by nlinarith only [hs0,hs,hratio₁]
              have hh := mul_le_mul_of_nonneg_left hL4 hK
              nlinarith only [hs,hratio₁,hh]) hnum₁
        · have hL6 : 6 ≤ L := by linarith only [h6]
          exact interval_coefficient H (9/8) s L (16/5) K₂ R hH (by norm_num)
            hs0 hL (by norm_num) hK₂ (by nlinarith only [h10])
            (by
              have hK : 0 ≤ K₂^2-1 := by nlinarith only [hs0,hs,hratio₂]
              have hh := mul_le_mul_of_nonneg_left hL6 hK
              nlinarith only [hs,hratio₂,hh]) hnum₂
      have hg : g ≤ (H+(9/8)/Real.sqrt L)*(t : ℝ) := by
        have hh := hhalf.trans (add_le_add le_rfl hceil)
        convert hh using 1 <;> ring
      apply (le_div_iff₀ hrootS).mpr
      calc
        g*Real.sqrt (s+L) ≤ ((H+(9/8)/Real.sqrt L)*(t : ℝ))*Real.sqrt (s+L) :=
          mul_le_mul_of_nonneg_right hg hrootS.le
        _ = ((H+(9/8)/Real.sqrt L)*Real.sqrt (s+L))*(t : ℝ) := by ring
        _ ≤ R*(t : ℝ) := mul_le_mul_of_nonneg_right hcoef ht0
    · have hL10 : 10 ≤ L := by linarith only [h10]
      have hg : g ≤ (B+9/8)*(t : ℝ)/Real.sqrt L := by
        have hh := hlog.trans (add_le_add le_rfl hceil)
        convert hh using 1 <;> ring
      have hcoef : (B+9/8)*Real.sqrt (s+L) ≤ R*Real.sqrt L := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        rw [mul_pow,mul_pow,Real.sq_sqrt (by linarith only [hs0,hL]),Real.sq_sqrt hL.le]
        have hS : 0 ≤ S := hs0.trans hs
        have hprod := mul_nonneg (sq_nonneg (B+9/8)) hS
        have hcoeff : (B+9/8)^2 ≤ R^2 := by nlinarith only [hlarge,hprod]
        have hh := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ L-10 by linarith only [hL10])
        have hsMul := mul_le_mul_of_nonneg_left hs (sq_nonneg (B+9/8))
        nlinarith only [hlarge,hh,hsMul]
      apply (le_div_iff₀ hrootS).mpr
      calc
        g*Real.sqrt (s+L) ≤ ((B+9/8)*(t : ℝ)/Real.sqrt L)*Real.sqrt (s+L) :=
          mul_le_mul_of_nonneg_right hg hrootS.le
        _ = ((B+9/8)*Real.sqrt (s+L))*(t : ℝ)/Real.sqrt L := by ring
        _ ≤ (R*Real.sqrt L)*(t : ℝ)/Real.sqrt L :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef ht0) hrootL.le
        _ = R*(t : ℝ) := by field_simp [hrootL.ne']

theorem five (t : ℕ) (ht : 8 ≤ t) (s g : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 7/3)
    (hhalf : g ≤ (7/8)*(t : ℝ)+(⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ))
    (hlog : g ≤ (13/5)*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ 5*(t : ℝ)/Real.sqrt (s+Real.logb 2 (t : ℝ)) :=
  aggregate t ht 5 (7/8) (13/5) (7/3) (4/3) (6/5) s g
    (by norm_num) (by norm_num) (by norm_num) hs0 hs
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hhalf hlog

theorem seven (t : ℕ) (ht : 8 ≤ t) (s g : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 3)
    (hhalf : g ≤ (5/8)*(t : ℝ)+(⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ))
    (hlog : g ≤ (11/5)*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ 7*(t : ℝ)/Real.sqrt (s+Real.logb 2 (t : ℝ)) :=
  aggregate t ht 7 (5/8) (11/5) 3 (4/3) (5/4) s g
    (by norm_num) (by norm_num) (by norm_num) hs0 hs
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hhalf hlog

theorem nine (t : ℕ) (ht : 8 ≤ t) (s g : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 10/3)
    (hhalf : g ≤ (15/8)*(t : ℝ)+(⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ))
    (hlog : g ≤ (29/5)*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ 9*(t : ℝ)/Real.sqrt (s+Real.logb 2 (t : ℝ)) :=
  aggregate t ht 9 (15/8) (29/5) (10/3) (11/8) (5/4) s g
    (by norm_num) (by norm_num) (by norm_num) hs0 hs
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hhalf hlog

end SymmetricSubgroupAsymptotics.SmallAffineJointLargePrimaryNumerics
