import SymmetricSubgroupAsymptotics.MarkerNormalizedKernel
import SymmetricSubgroupAsymptotics.MarkerDefectSum

/-!
# Decay of the complete defined positive-defect marker row

The finite Gaussian/coefficient kernel and its complete parameter fibres
are defined in MarkerNormalizedKernel. Here their proved polynomial
prefactor is absorbed uniformly in the defect. No pointwise kernel bound
or physical subgroup-count premise is an input to the final theorem.
Physical coverage by the presentation kernel remains a separate statement.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.MarkerNormalizedRow

open MarkerNormalizedKernel

theorem polynomial_prefactor_le (N D : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N)
    (hphi : eulerProduct⁻¹^2 ≤ (N:ℝ)+2) :
    ((2*D+2:ℕ):ℝ)^2 * defectEnvelope N D ≤ 
      ((N:ℝ)+2)^(31*D) * (2:ℝ)^(-13*(N:ℝ)*D/60) := by
  let x : ℝ := (N:ℝ)+2
  have hx : 2 ≤ x := by
    dsimp [x]
    linarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  have hD' : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hDN' : (D:ℝ) ≤ N := by exact_mod_cast hDN
  have hbin : (((2*D+2:ℕ):ℝ)^2) ≤ x^4 := by
    have hb : ((2*D+2:ℕ):ℝ) ≤ x^2 := by
      push_cast
      dsimp [x]
      nlinarith [sq_nonneg (N:ℝ)]
    have h := pow_le_pow_left₀ (by positivity) hb 2
    simpa only [← pow_mul] using h
  have hmiddle : (N:ℝ)+1 ≤ x := by dsimp [x]; linarith
  have hpoint : (2*(N:ℝ))^(3*D) ≤ x^(6*D) := by
    have hb : 2*(N:ℝ) ≤ x^2 := by
      dsimp [x]
      nlinarith [sq_nonneg (N:ℝ)]
    have h := pow_le_pow_left₀ (by positivity) hb (3*D)
    simpa only [← pow_mul,show 2*(3*D)=6*D by omega] using h
  have hpair : (N:ℝ)^(3*D) ≤ x^(3*D) :=
    pow_le_pow_left₀ (by positivity) (by dsimp [x]; linarith) _
  have hlinear : (2:ℝ)^(15*(D:ℝ)+1/4) ≤ x^(15*D+1) := by
    calc
      _ ≤ (2:ℝ)^(((15*D+1:ℕ):ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast
        linarith
      _ = (2:ℝ)^(15*D+1) := Real.rpow_natCast _ _
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hx _
  have hpoly : ((2*D+2:ℕ):ℝ)^2 * eulerProduct⁻¹^2 * ((N:ℝ)+1) *
      (2*(N:ℝ))^(3*D) * (N:ℝ)^(3*D) * (2:ℝ)^(15*(D:ℝ)+1/4) ≤ 
      x^4*x*x*x^(6*D)*x^(3*D)*x^(15*D+1) := by
    apply mul_le_mul _ hlinear (by positivity) (by positivity)
    apply mul_le_mul _ hpair (by positivity) (by positivity)
    apply mul_le_mul _ hpoint (by positivity) (by positivity)
    apply mul_le_mul _ hmiddle (by positivity) (by positivity)
    exact mul_le_mul hbin hphi (by positivity) (by positivity)
  have hpowers : x^4*x*x*x^(6*D)*x^(3*D)*x^(15*D+1)=x^(24*D+7) := by
    calc
      _ = x^(4+1+1+6*D+3*D+(15*D+1)) := by
        simp only [pow_add,pow_one]
      _ = _ := by congr 1; omega
  have he : -13*(N:ℝ)*D/60+15*D+1/4 =
      (-13*(N:ℝ)*D/60)+(15*(D:ℝ)+1/4) := by ring
  calc
    _ = (((2*D+2:ℕ):ℝ)^2 * eulerProduct⁻¹^2 * ((N:ℝ)+1) *
        (2*(N:ℝ))^(3*D) * (N:ℝ)^(3*D) * (2:ℝ)^(15*(D:ℝ)+1/4)) *
        (2:ℝ)^(-13*(N:ℝ)*D/60) := by
      unfold defectEnvelope
      rw [he,Real.rpow_add (by norm_num : (0:ℝ)<2)]
      ring
    _ ≤ (x^4*x*x*x^(6*D)*x^(3*D)*x^(15*D+1))*
        (2:ℝ)^(-13*(N:ℝ)*D/60) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ ≤ _ := by
      rw [hpowers]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_right₀ (by linarith) (by omega)

def logarithmicConstant : ℝ := 31/Real.log 2

theorem logarithmicConstant_nonneg : 0 ≤ logarithmicConstant := by
  unfold logarithmicConstant
  exact div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le

theorem polynomial_as_log_power (N D : ℕ) :
    ((N:ℝ)+2)^(31*D) =
      (2:ℝ)^(logarithmicConstant*D*Real.log ((N:ℝ)+2)) := by
  have he : logarithmicConstant*D*Real.log ((N:ℝ)+2) =
      Real.logb 2 ((N:ℝ)+2)*((31*D:ℕ):ℝ) := by
    unfold logarithmicConstant Real.logb
    push_cast
    ring
  rw [he,Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) (by positivity),
    Real.rpow_natCast]

/-- This envelope is derived for the actual defined defect sum; it is
not the arbitrary-array envelope premise of MarkerDefectSum. -/
theorem eventually_actual_defect_envelope :
    ∀ᶠ N : ℕ in atTop, ∀ epsilon D : ℕ, D ∈ Finset.Icc 1 N →
      defectKernel N epsilon D ≤ 
        (2:ℝ)^(-13*(N:ℝ)*D/60+
          logarithmicConstant*D*Real.log ((N:ℝ)+2)) := by
  obtain ⟨n0,hn0⟩ := exists_nat_gt (eulerProduct⁻¹^2)
  filter_upwards [eventually_ge_atTop n0] with N hN
  intro epsilon D hD
  have hD1 := (Finset.mem_Icc.mp hD).1
  have hDN := (Finset.mem_Icc.mp hD).2
  have hN' : (n0:ℝ) ≤ N := by exact_mod_cast hN
  have hphi : eulerProduct⁻¹^2 ≤ (N:ℝ)+2 := by linarith
  apply (defectKernel_le N epsilon D hD1).trans
  apply (polynomial_prefactor_le N D hD1 hDN hphi).trans_eq
  rw [polynomial_as_log_power,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

def positiveDefectRow (N epsilon : ℕ) : ℝ :=
  ∑ D ∈ Finset.Icc 1 N, defectKernel N epsilon D

/-- Complete positive-defect numerical row, with no supplied envelope,
Gaussian, profile-cardinality, or subgroup-count hypothesis. -/
theorem eventually_positiveDefectRow_le (epsilon : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      positiveDefectRow N epsilon ≤ (2:ℝ)^(-(N:ℝ)/10) := by
  apply MarkerDefectSum.eventually_defect_sum_le logarithmicConstant
    logarithmicConstant_nonneg (fun N D => defectKernel N epsilon D)
  filter_upwards [eventually_actual_defect_envelope] with N hN
  intro D hD
  exact hN epsilon D hD

/-- One eventual threshold works simultaneously at the two actual parities. -/
theorem eventually_both_parities :
    ∀ᶠ N : ℕ in atTop, ∀ epsilon : ℕ, epsilon ≤ 1 →
      positiveDefectRow N epsilon ≤ (2:ℝ)^(-(N:ℝ)/10) := by
  filter_upwards [eventually_positiveDefectRow_le 0,
    eventually_positiveDefectRow_le 1] with N hzero hone
  intro epsilon hepsilon
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hepsilon with h | h
  · simpa only [h] using hzero
  · simpa only [h] using hone

end SymmetricSubgroupAsymptotics.MarkerNormalizedRow
