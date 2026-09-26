import SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles
import SymmetricSubgroupAsymptotics.BinaryMixtureHallDecay
import SymmetricSubgroupAsymptotics.GaussianUniformLower

/-! The actual original thirteen-color Hall branch at fixed parameters.
Complete original normalizer/factorial weights and the entire support
shift 2a+4T are retained. Source order is bounded by the proved 7T cap;
no original subgroup count, rank bound or finite profile list is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierHallProfiles

open BinaryCarrierOriginalCyclicFourHall BinaryCarrierSmallSupportProfiles
open BinaryCarrierParameterProfiles BinaryMixtureNumerics

def modelUpper (R a T : ℕ) : ℝ :=
  2 * (eulerProduct⁻¹)^5 * hallPolynomial R R a (7*T) *
    (2 : ℝ)^(hallQuadratic R a (7*T))

theorem modelUpper_nonneg (R a T : ℕ) : 0 ≤ modelUpper R a T := by
  unfold modelUpper hallPolynomial
  positivity [euler_positive]

private theorem hall_bound_le (R c a u T : ℕ) (hc : c≤R) (hu : u≤7*T) :
    BinaryCriticalCyclicFourHall.bound R c a u ≤ modelUpper R a T := by
  have hc' : (c : ℝ)≤R := by exact_mod_cast hc
  have hu' : (u : ℝ)≤7*(T : ℝ) := by exact_mod_cast hu
  have hp : hallPolynomial R c a u ≤ hallPolynomial R R a (7*T) := by
    unfold hallPolynomial
    push_cast
    gcongr <;> linarith
  have h₁ : ((a : ℝ)+u+7)^2 ≤ ((a : ℝ)+7*T+7)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h₂ : ((R : ℝ)+u+a)^2 ≤ ((R : ℝ)+a+7*T)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have he : (((a : ℝ)+u+7)^2)/3 + ((a : ℝ)^2+((R : ℝ)+u+a)^2)/4 ≤
      hallQuadratic R a (7*T) := by
    unfold hallQuadratic
    push_cast
    linarith
  calc
    _ = (2 * (eulerProduct⁻¹)^5 * hallPolynomial R c a u) *
        (2 : ℝ)^((((a : ℝ)+u+7)^2)/3 + ((a : ℝ)^2+((R : ℝ)+u+a)^2)/4) := by
      unfold BinaryCriticalCyclicFourHall.bound hallPolynomial
      ring
    _ ≤ (2 * (eulerProduct⁻¹)^5 * hallPolynomial R R a (7*T)) *
        (2 : ℝ)^(hallQuadratic R a (7*T)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity [euler_positive]))
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)
        (by positivity) (by unfold hallPolynomial; positivity [euler_positive])
    _ = _ := rfl

/-- A bin's uniform model bound is proved from each original model's
actual master epimorphism and exact source order, not supplied as input. -/
theorem modelCount_le (R a T : ℕ) (p : CriticalProfile) (hp : p.rank=R)
    (q : Target → ℕ) (hq : q ∈ profilesAtParameters a T) :
    modelCount p q ≤ modelUpper R a T := by
  obtain ⟨ha,hT⟩ := (mem_profilesAtParameters a T q).mp hq
  let m : CarrierTarget → ℕ := fun t => q (some t)
  let occurrences : Fin (Fintype.card (Σ t, Fin (m t))) ≃ (Σ t, Fin (m t)) :=
    (Fintype.equivFin (Σ t, Fin (m t))).symm
  have h := modelFamily_card_le_hall p (q none) m occurrences (fun _ => True)
  change (Nat.card (BinaryCarrierMixedProfile.ModelFamily points action p
    (multiplicity (q none) (fun t => q (some t))) (fun _ => True)) : ℝ) ≤
      BinaryCriticalCyclicFourHall.bound p.rank (p.d8+p.e8) (q none) (carrierOrder m) at h
  rw [multiplicity_split, hp, ha] at h
  have hu : carrierOrder m≤7*T := by
    have hu := carrierOrder_le_scale m occurrences
    simpa only [m, hT] using hu
  have hc : p.d8+p.e8≤R := by
    have hc := terminalCritical_two_card_le_rank p.abelianRank (criticalProfileNonabelianChoice p)
    simp only [criticalProfile_product_rank, CriticalProfileNonabelianIndex,
      Fintype.card_sum, Fintype.card_fin, hp] at hc
    omega
  exact h.trans (hall_bound_le R _ a _ T hc hu)

/-- All profiles in the exact (a,T) bin are included with their original
weights. The entire removed half-support is paid in the critical shift. -/
theorem weightedSum_div_le (R a T : ℕ) :
    weightedSum R a T /
      ((criticalCoefficient (R+2*a+4*T) : ℝ) * (binaryGaussianSum (R+2*a+4*T) : ℝ)) ≤
      (Real.exp 13 * (2*((R+2*a+4*T : ℕ) : ℝ))^(2*a+4*T) * modelUpper R a T) /
        (eulerProduct * (2 : ℝ)^(((R+2*a+4*T : ℕ) : ℝ)^2/4-1/4)) := by
  let n := R+2*a+4*T
  have hG : (0 : ℝ) < binaryGaussianSum n := by
    exact_mod_cast binaryGaussianSum_pos n
  have hM : 0 ≤ modelUpper R a T / (binaryGaussianSum n : ℝ) :=
    div_nonneg (modelUpper_nonneg R a T) hG.le
  have h := original_shifted_profile_count_sum_le R (2*a+4*T)
    (fun _ => profilesAtParameters a T) modelCount
    (modelUpper R a T / (binaryGaussianSum n : ℝ)) hM (by
      intro p hp q hq
      have hp' := (mem_criticalProfiles R p).mp hp
      calc
        _ ≤ modelUpper R a T := modelCount_le R a T p hp' q hq
        _ = (binaryGaussianSum (R+(2*a+4*T)) : ℝ) *
            (modelUpper R a T / (binaryGaussianSum n : ℝ)) := by
          have hn : R+(2*a+4*T)=n := by dsimp [n]; omega
          rw [hn]
          field_simp [hG.ne'])
  have hlower := binaryGaussianSum_quadratic_lower n
  have hpos : 0 < eulerProduct * (2 : ℝ)^((n : ℝ)^2/4-1/4) := by
    positivity [euler_positive]
  calc
    _ ≤ Real.exp 13 * (2*(n : ℝ))^(2*a+4*T) *
        (modelUpper R a T / (binaryGaussianSum n : ℝ)) := by
      simpa only [weightedSum, n, Nat.add_assoc] using h
    _ = (Real.exp 13 * (2*(n : ℝ))^(2*a+4*T) * modelUpper R a T) /
        (binaryGaussianSum n : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity [modelUpper_nonneg R a T]) hpos hlower

/-- Uniform normalized weight decay throughout the small-carrier Hall
regime, including all original profiles in each exact bin. -/
theorem eventually_weightedSum_div_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R a T : ℕ,
      n=R+2*a+4*T → 1≤a → 140*T≤a →
      weightedSum R a T /
        ((criticalCoefficient n : ℝ) * (binaryGaussianSum n : ℝ)) ≤
          (2 : ℝ)^(-(n : ℝ)/50) := by
  filter_upwards [eventually_normalized_hall_with_gaussian_lower eulerProduct euler_positive]
    with n hn
  intro R a T hN ha hTa
  have h := weightedSum_div_le R a T
  rw [← hN] at h
  apply h.trans
  exact hn R R a (7*T) T hN le_rfl ha le_rfl hTa

/-- This is the literal original physical bin; its factorial is cancelled
against the same exact benchmark, with no source normalizer substituted. -/
theorem eventually_physical_card_div_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R a T : ℕ,
      n=R+2*a+4*T → 1≤a → 140*T≤a →
      (Nat.card (PhysicalFamily R a T (Fin (2*(R+2*a+4*T)))) : ℝ) /
        exactBenchmark (2*(R+2*a+4*T)) ≤ (2 : ℝ)^(-(n : ℝ)/50) := by
  filter_upwards [eventually_weightedSum_div_le] with n hn
  intro R a T hN ha hTa
  apply (card_div_benchmark_le_weightedSum R a T).trans
  simpa only [hN] using hn R a T hN ha hTa

end SymmetricSubgroupAsymptotics.BinaryCarrierHallProfiles
