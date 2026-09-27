import SymmetricSubgroupAsymptotics.MarkerGeometry
import SymmetricSubgroupAsymptotics.MarkerQuadraticDeficit
import SymmetricSubgroupAsymptotics.MarkerPairFactorial
import SymmetricSubgroupAsymptotics.RepeatedMarkerProfileBound
import SymmetricSubgroupAsymptotics.FusionPointingRatio

/-!
# The explicit normalized marker presentation kernel

The complete positive-profile sum, original 6^g f! factor, guarded parity
coefficient, Gaussian ratio, and falling-factorial pair cost are all
defined here. Their envelope is proved from these definitions, not supplied
as a counting premise. Physical coverage remains a separate application.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.MarkerNormalizedKernel

open MarkerGeometry RepeatedMarkerAllocationWeights RepeatedMarkerProfileBound

theorem critical_le_parity (epsilon M : ℕ) :
    criticalCoefficient M ≤ analyticParityCoefficient epsilon M := by
  unfold analyticParityCoefficient
  apply le_add_of_nonneg_right
  split_ifs
  · exact div_nonneg (criticalCoefficient_nonneg _) (by norm_num)
  · exact le_rfl

theorem coefficient_ratio_le (epsilon M h : ℕ) :
    (criticalCoefficient M:ℝ)/(analyticParityCoefficient epsilon (M+h):ℝ) ≤ 
      (2*((M+h:ℕ):ℝ))^h := by
  have hr : criticalCoefficient M / analyticParityCoefficient epsilon (M+h) ≤ 
      (2*((M+h:ℕ):ℚ))^h := by
    apply (div_le_iff₀ (analyticParityCoefficient_positive _ _)).mpr
    exact (critical_le_parity epsilon M).trans
      (analyticParityCoefficient_shift_le epsilon M h)
  exact_mod_cast hr

/-- Cross-parity factorial cancellation keeps the original odd guard. -/
theorem factorial_benchmark_ratio (N epsilon M : ℕ) (hepsilon : epsilon ≤ 1) :
    (((2*N+epsilon).factorial:ℝ)/(2*M).factorial) *
        exactBenchmark (2*M)/exactBenchmark (2*N+epsilon) =
      ((criticalCoefficient M:ℝ)/(analyticParityCoefficient epsilon N:ℝ)) *
        ((binaryGaussianSum M:ℝ)/(binaryGaussianSum N:ℝ)) := by
  have hm : halfDegree (2*M)=M := by unfold halfDegree; omega
  have hn : halfDegree (2*N+epsilon)=N := by unfold halfDegree; omega
  have hpm : parity (2*M)=0 := by unfold parity; omega
  have hpn : parity (2*N+epsilon)=epsilon := by unfold parity; omega
  unfold exactBenchmark
  rw [← analyticParityCoefficient_halfDegree (2*M),
    ← analyticParityCoefficient_halfDegree (2*N+epsilon),hm,hn,hpm,hpn]
  have hzero : analyticParityCoefficient 0 M=criticalCoefficient M := by
    simp [analyticParityCoefficient]
  rw [hzero]
  have hfm : ((2*M).factorial:ℝ)≠0 := by positivity
  have hfn : ((2*N+epsilon).factorial:ℝ)≠0 := by positivity
  field_simp

def markerWeight (g f q : ℕ) : ℝ := (2:ℝ)^q / ((6:ℝ)^g*(f.factorial:ℝ))

theorem markerWeight_nonneg (g f q : ℕ) : 0 ≤ markerWeight g f q := by
  unfold markerWeight
  positivity

theorem markerWeight_le_one (g f q : ℕ) (hq : q ≤ g) : markerWeight g f q ≤ 1 := by
  unfold markerWeight
  apply (div_le_one (by positivity)).mpr
  have hp : (2:ℝ)^q ≤ (6:ℝ)^g :=
    (pow_le_pow_right₀ (by norm_num) hq).trans
      (pow_le_pow_left₀ (by norm_num) (by norm_num) g)
  have hf : (1:ℝ) ≤ f.factorial := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos f)
  exact hp.trans (le_mul_of_one_le_right (by positivity) hf)

theorem profile_sum_nonneg (g q : ℕ) :
    0 ≤ (markerProfileSum (Q := Fin q) g:ℝ) := by
  have h : (0:ℚ) ≤ markerProfileSum (Q := Fin q) g := by
    unfold markerProfileSum profileSum
    apply Finset.sum_nonneg
    intro a _
    apply Finset.prod_nonneg
    intro i _
    positivity
  exact_mod_cast h

/-- The larger presentation kernel uses (M)_q, retaining rather than
dividing out the factorial of an arbitrary selected-label presentation. -/
def profileKernel {N epsilon : ℕ} (s : Parameters N epsilon) : ℝ :=
  (((criticalCoefficient s.M:ℝ)/(analyticParityCoefficient epsilon N:ℝ)) *
    ((binaryGaussianSum s.M:ℝ)/(binaryGaussianSum N:ℝ))) *
    (markerWeight s.g s.f s.q * (markerProfileSum (Q := Fin s.q) s.g:ℝ)) *
    (s.M.descFactorial s.q:ℝ)

theorem profileKernel_nonneg {N epsilon : ℕ} (s : Parameters N epsilon) :
    0 ≤ profileKernel s := by
  have hc : 0 ≤ (criticalCoefficient s.M:ℝ) := by
    exact_mod_cast criticalCoefficient_nonneg s.M
  have ha : 0 ≤ (analyticParityCoefficient epsilon N:ℝ) := by
    exact_mod_cast (analyticParityCoefficient_positive epsilon N).le
  have hg : 0 ≤ (binaryGaussianSum s.M:ℝ) := by
    exact_mod_cast (binaryGaussianSum_pos s.M).le
  have hG : 0 ≤ (binaryGaussianSum N:ℝ) := by
    exact_mod_cast (binaryGaussianSum_pos N).le
  have hw := markerWeight_nonneg s.g s.f s.q
  have hH := profile_sum_nonneg s.g s.q
  unfold profileKernel
  positivity

/-- Every parameter is the actual support parameter; in particular the
repeats are g-q and the entire positive profile sum is used. -/
theorem profileKernel_le {N epsilon : ℕ} (s : Parameters N epsilon) :
    profileKernel s ≤ 
      eulerProduct⁻¹^2 * (s.M+1) * (2*(N:ℝ))^(s.defect+s.repeats) * (N:ℝ)^s.q *
        (2:ℝ)^(-13*(N:ℝ)*s.defect/60+6*s.repeats+s.g+1/4) := by
  have hdegree : s.M+(s.defect+s.repeats)=N := by
    have h := s.degree_balance
    omega
  have hreal : (N:ℝ)=(s.M:ℝ)+s.defect+s.repeats := by
    exact_mod_cast s.degree_balance
  have hc := coefficient_ratio_le epsilon s.M (s.defect+s.repeats)
  rw [hdegree] at hc
  have hG : (binaryGaussianSum s.M:ℝ)/(binaryGaussianSum N:ℝ) ≤ 
      eulerProduct⁻¹^2*(s.M+1)*
        (2:ℝ)^(-(N:ℝ)*((s.defect:ℝ)+s.repeats)/2+
          ((s.defect:ℝ)+s.repeats)^2/4+1/4) := by
    have h := fusionGaussianRatio_le s.M (s.defect+s.repeats)
    rw [hdegree] at h
    simp only [Nat.cast_add] at h
    have he : -((s.defect:ℝ)+s.repeats)*s.M/2-
        ((s.defect:ℝ)+s.repeats)^2/4+1/4 =
        -(N:ℝ)*((s.defect:ℝ)+s.repeats)/2+
          ((s.defect:ℝ)+s.repeats)^2/4+1/4 := by
      rw [hreal]
      ring
    rw [he] at h
    exact h
  have hH : markerWeight s.g s.f s.q *
      (markerProfileSum (Q := Fin s.q) s.g:ℝ) ≤ 
      (2:ℝ)^(Real.logb 2 3*(s.repeats:ℝ)^2/4+6*s.repeats+s.g) := by
    apply le_trans ((mul_le_mul_of_nonneg_right
      (markerWeight_le_one s.g s.f s.q s.q_le_g) (profile_sum_nonneg s.g s.q)).trans_eq
      (one_mul _))
    simpa only [Fintype.card_fin,Parameters.repeats] using
      markerProfileSum_le_binary (Q := Fin s.q) s.g
  have hM : s.M ≤ N := by have h := s.degree_balance; omega
  have hp : (s.M.descFactorial s.q:ℝ) ≤ (N:ℝ)^s.q := by
    exact_mod_cast (Nat.descFactorial_le_pow s.M s.q).trans
      (Nat.pow_le_pow_left hM s.q)
  have hquad := MarkerQuadraticDeficit.quadratic_le
    (N := (N:ℝ)) (D := (s.defect:ℝ)) (k := (s.repeats:ℝ))
    (lambda := Real.logb 2 3) (by positivity)
    (by exact_mod_cast s.defect_le) (by positivity)
    (by exact_mod_cast s.repeats_le_two_defect)
    (by
      have h : s.repeats+s.defect ≤ N := by
        have hb := s.degree_balance
        omega
      have hr : (s.repeats:ℝ)+s.defect ≤ N := by exact_mod_cast h
      linarith)
    logb_two_three_lt.le
  calc
    _ ≤ ((2*(N:ℝ))^(s.defect+s.repeats) *
        (eulerProduct⁻¹^2*(s.M+1)*
          (2:ℝ)^(-(N:ℝ)*((s.defect:ℝ)+s.repeats)/2+
            ((s.defect:ℝ)+s.repeats)^2/4+1/4))) *
        (2:ℝ)^(Real.logb 2 3*(s.repeats:ℝ)^2/4+6*s.repeats+s.g) * (N:ℝ)^s.q := by
      unfold profileKernel
      apply mul_le_mul _ hp (by positivity) (by positivity)
      apply mul_le_mul _ hH
        (mul_nonneg (markerWeight_nonneg _ _ _) (profile_sum_nonneg _ _)) (by positivity)
      apply mul_le_mul hc hG
        (div_nonneg (by exact_mod_cast (binaryGaussianSum_pos s.M).le)
          (by exact_mod_cast (binaryGaussianSum_pos N).le)) (by positivity)
    _ = eulerProduct⁻¹^2*(s.M+1)*(2*(N:ℝ))^(s.defect+s.repeats)*(N:ℝ)^s.q *
        (2:ℝ)^(MarkerQuadraticDeficit.quadratic N s.defect s.repeats (Real.logb 2 3)+
          6*s.repeats+s.g+1/4) := by
      have he : MarkerQuadraticDeficit.quadratic (N:ℝ) s.defect s.repeats (Real.logb 2 3)+
          6*s.repeats+s.g+1/4 =
          (-(N:ℝ)*((s.defect:ℝ)+s.repeats)/2+((s.defect:ℝ)+s.repeats)^2/4+1/4)+
          (Real.logb 2 3*(s.repeats:ℝ)^2/4+6*s.repeats+s.g) := by
        unfold MarkerQuadraticDeficit.quadratic
        ring
      rw [he,Real.rpow_add (by norm_num : (0:ℝ)<2)
        (-(N:ℝ)*((s.defect:ℝ)+s.repeats)/2+((s.defect:ℝ)+s.repeats)^2/4+1/4)
        (Real.logb 2 3*(s.repeats:ℝ)^2/4+6*s.repeats+s.g)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith

/-- A common expression for every profile with the same positive defect. -/
def defectEnvelope (N D : ℕ) : ℝ :=
  eulerProduct⁻¹^2*((N:ℝ)+1)*(2*(N:ℝ))^(3*D)*(N:ℝ)^(3*D)*
    (2:ℝ)^(-13*(N:ℝ)*D/60+15*D+1/4)

theorem defectEnvelope_nonneg (N D : ℕ) : 0 ≤ defectEnvelope N D := by
  unfold defectEnvelope
  positivity

theorem profileKernel_le_defectEnvelope {N epsilon : ℕ}
    (s : Parameters N epsilon) (hD : 1 ≤ s.defect) :
    profileKernel s ≤ defectEnvelope N s.defect := by
  have hN : 1 ≤ N := hD.trans s.defect_le
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hM : (s.M:ℝ) ≤ N := by
    have h : s.M ≤ N := by have hb := s.degree_balance; omega
    exact_mod_cast h
  have hh : s.defect+s.repeats ≤ 3*s.defect := by
    have h := s.repeats_le_two_defect
    omega
  have hq := s.selected_le_three_defect hD
  have hlin : 6*s.repeats+s.g ≤ 15*s.defect := by
    have hk := s.repeats_le_two_defect
    have hg := s.markers_le
    omega
  have hlin' : 6*(s.repeats:ℝ)+s.g ≤ 15*s.defect := by exact_mod_cast hlin
  apply (profileKernel_le s).trans
  unfold defectEnvelope
  apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    (by positivity) (by positivity)
  apply mul_le_mul _ (pow_le_pow_right₀ hN' hq) (by positivity) (by positivity)
  apply mul_le_mul _ (pow_le_pow_right₀ (by linarith) hh) (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

local instance defectFibreFinite (N epsilon D : ℕ) : Finite (DefectFibre N epsilon D) :=
  Finite.of_injective profileCode profileCode_injective

/-- The complete original natural parameter fibre, rather than a supplied
finite collection with a postulated cardinality bound. -/
def defectKernel (N epsilon D : ℕ) : ℝ :=
  ∑ s : DefectFibre N epsilon D, profileKernel s.val

theorem defectKernel_nonneg (N epsilon D : ℕ) : 0 ≤ defectKernel N epsilon D :=
  Finset.sum_nonneg (fun s _ => profileKernel_nonneg s.val)

theorem defectKernel_le (N epsilon D : ℕ) (hD : 1 ≤ D) :
    defectKernel N epsilon D ≤ ((2*D+2:ℕ):ℝ)^2 * defectEnvelope N D := by
  unfold defectKernel
  calc
    _ ≤ ∑ _s : DefectFibre N epsilon D, defectEnvelope N D := by
      apply Finset.sum_le_sum
      intro s _
      have h := profileKernel_le_defectEnvelope s.val (by simpa only [s.property] using hD)
      simpa only [s.property] using h
    _ = (Nat.card (DefectFibre N epsilon D):ℝ)*defectEnvelope N D := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (defectEnvelope_nonneg N D)
      exact_mod_cast card_defect_fibre_le N epsilon D

end SymmetricSubgroupAsymptotics.MarkerNormalizedKernel
