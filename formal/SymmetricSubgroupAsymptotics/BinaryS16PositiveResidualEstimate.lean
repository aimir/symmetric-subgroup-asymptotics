import SymmetricSubgroupAsymptotics.BinaryS16DecorationNumerics
import SymmetricSubgroupAsymptotics.BinaryS16FinalFibreClosure

/-!
# Unconditional scalar bound for the positive S16 residual

The final fibre reflection supplies the exact packed count.  The retained
window then places every target bin in one of the small-support, Hall, or
carrier-reserve estimates.  This file performs both finite sums and absorbs
their cubic index count.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryS16PositiveResidualEstimate

open BinaryCarrierActualDecoratedTransport
open BinaryCarrierParameterProfiles
open BinaryCarrierParameterUnion
open BinaryS16DecorationNumerics
open BinaryS16DirectFixedSupportClosure

/-- The rate left after summing the support/bin indices. -/
def rate : ℝ := 29/2980864

theorem rate_pos : 0 < rate := by norm_num [rate]

def decoratedTerm (N Cold : ℕ) (b : RetainedBin N Cold) : ℝ :=
  (((2*N+2)^(10*(2*Cold)) : ℕ) : ℝ) *
    ((Nat.card (PhysicalFamily
      (N-binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2*N))) : ℝ) /
      exactBenchmark (2*N))

def packedRatio (N : ℕ) : ℝ :=
  ∑ C : SupportIndex N, ∑ b : RetainedBin N C.1.1,
    decoratedTerm N C.1.1 b

theorem supportIndex_card_le (N : ℕ) : Nat.card (SupportIndex N) ≤ N+1 := by
  calc
    Nat.card (SupportIndex N) ≤ Nat.card (Fin (N+1)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = N+1 := Nat.card_fin (N+1)

theorem retainedBin_card_le (N Cold : ℕ) :
    Nat.card (RetainedBin N Cold) ≤ (N+1)^2 := by
  calc
    Nat.card (RetainedBin N Cold) ≤ Nat.card (bins N (fun _ _ ↦ True)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ ≤ (N+1)^2 := bins_card_le N (fun _ _ ↦ True)

private theorem weak_small_rate (N : ℕ) :
    (2 : ℝ)^(-(N : ℝ)/8) ≤ (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

private theorem weak_hall_rate (N : ℕ) :
    (2 : ℝ)^(-(N : ℝ)/50) ≤ (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- Every literal retained bin pays its complete S16 decoration before the
three regimes are coarsened to a common rate. -/
theorem eventually_decoratedTerm_le :
    ∀ᶠ N : ℕ in atTop, ∀ C : SupportIndex N,
      ∀ b : RetainedBin N C.1.1,
        decoratedTerm N C.1.1 b ≤
          (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
  filter_upwards [BinaryCarrierParameterSmallSupport.eventually_physical_card_div_le,
    eventually_small_support_decoration, eventually_hall_bin_decoration,
    eventually_reserve_bin_decoration] with N hsmall hsmallDecoration hhall hreserve
  intro C b
  let a : ℕ := b.1.1.1
  let T : ℕ := b.1.1.2
  let S : ℕ := binSupport b.1
  let R : ℕ := N-S
  have hSpos : 0<S := binSupport_pos b.1
  have hSle : S≤N := binSupport_le b.1
  have hS : S=2*a+4*T := rfl
  have hdegree : R+2*a+4*T=N := by
    omega
  have hret : C.1.1≤4*S := by
    exact retained_quarter b
  have hfactor : 10*(2*C.1.1)=20*C.1.1 := by omega
  unfold decoratedTerm
  rw [hfactor]
  by_cases hcut : (S : ℝ) ≤ Real.sqrt (N : ℝ)/4
  · have hp := hsmall R a T hdegree.symm hSpos hcut
    have hp' :
        (Nat.card (PhysicalFamily R a T (Fin (2*N))) : ℝ) /
            exactBenchmark (2*N) ≤ (2 : ℝ)^(-(N : ℝ)/4) := by
      simpa only [hdegree] using hp
    have hmul := mul_le_mul_of_nonneg_left hp'
      (show (0 : ℝ) ≤ (((2*N+2)^(20*C.1.1) : ℕ) : ℝ) by positivity)
    exact (hmul.trans (hsmallDecoration C.1.1 S hret hcut)).trans
      (weak_small_rate N)
  · by_cases hHall : 140*T≤a
    · have ha : 1≤a := by omega
      have h := hhall R a T C.1.1 hdegree.symm ha hHall hret
      simpa only [hdegree] using h.trans (weak_hall_rate N)
    · have h := hreserve R a T C.1.1 hdegree (Nat.lt_of_not_ge hHall)
          (lt_of_not_ge hcut) hret
      simpa only [hdegree] using h

theorem packedRatio_le_polynomial (N : ℕ)
    (hterm : ∀ C : SupportIndex N, ∀ b : RetainedBin N C.1.1,
      decoratedTerm N C.1.1 b ≤ (2 : ℝ)^(-(29/1490432)*(N : ℝ))) :
    packedRatio N ≤ ((N : ℝ)+1)^3 *
      (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
  have hpow : (0 : ℝ) ≤ (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by positivity
  calc
    packedRatio N ≤ ∑ C : SupportIndex N,
        ∑ _b : RetainedBin N C.1.1,
          (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
      unfold packedRatio
      exact Finset.sum_le_sum (fun C _ ↦ Finset.sum_le_sum (fun b _ ↦ hterm C b))
    _ = ∑ C : SupportIndex N,
        (Nat.card (RetainedBin N C.1.1) : ℝ) *
          (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
      apply Finset.sum_congr rfl
      intro C _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
    _ ≤ ∑ _C : SupportIndex N, ((N : ℝ)+1)^2 *
          (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro C _
      apply mul_le_mul_of_nonneg_right _ hpow
      exact_mod_cast retainedBin_card_le N C.1.1
    _ = (Nat.card (SupportIndex N) : ℝ) * (((N : ℝ)+1)^2 *
          (2 : ℝ)^(-(29/1490432)*(N : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
    _ ≤ ((N : ℝ)+1) * (((N : ℝ)+1)^2 *
          (2 : ℝ)^(-(29/1490432)*(N : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast supportIndex_card_le N
    _ = _ := by ring

/-- The exact natural packed sum, divided by the benchmark, is the real
double sum used by the numerical estimate. -/
theorem packedNat_div_eq_packedRatio (N : ℕ) :
    ((∑ C : SupportIndex N,
        (2*N+2)^(10*(2*C.1.1)) *
          ∑ b : RetainedBin N C.1.1,
            Nat.card (PhysicalFamily
              (N-binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2*N))) : ℕ) : ℝ) /
        exactBenchmark (2*N) = packedRatio N := by
  unfold packedRatio decoratedTerm
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro C _
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum]

theorem eventually_packedRatio_le :
    ∀ᶠ N : ℕ in atTop,
      packedRatio N ≤ (2 : ℝ)^(-rate*(N : ℝ)) := by
  filter_upwards [eventually_decoratedTerm_le,
    BinaryMixtureNumerics.eventually_polynomial_bins_le 3
      (29/1490432) (by norm_num : (0 : ℝ)<29/1490432)] with N hterm hpoly
  exact (packedRatio_le_polynomial N hterm).trans (by
    convert hpoly using 1 <;> norm_num [rate])

/-- Unconditional exponentially small normalized count for the complete
positive S16 residual family. -/
theorem eventually_positiveResidual_card_div_benchmark_le :
    ∀ᶠ N : ℕ in atTop,
      (Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ) /
        exactBenchmark (2*N) ≤ (2 : ℝ)^(-rate*(N : ℝ)) := by
  filter_upwards [eventually_packedRatio_le, eventually_ge_atTop 4] with N hpacked hN
  have hcount :=
    BinaryS16DirectPhysicalEncoding.positiveResidual_card_le_packed_sum_of_targetSubgroup_reflection
      hN (fun C ↦ BinaryS16FinalFibreClosure.reflectsTargetSubgroup C)
  have hreal :
      (Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ) ≤
        ((∑ C : SupportIndex N,
          (2*N+2)^(10*(2*C.1.1)) *
            ∑ b : RetainedBin N C.1.1,
              Nat.card (PhysicalFamily
                (N-binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2*N))) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  calc
    _ ≤ ((∑ C : SupportIndex N,
          (2*N+2)^(10*(2*C.1.1)) *
            ∑ b : RetainedBin N C.1.1,
              Nat.card (PhysicalFamily
                (N-binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2*N))) : ℕ) : ℝ) /
          exactBenchmark (2*N) :=
      div_le_div_of_nonneg_right hreal (exactBenchmark_pos _).le
    _ = packedRatio N := packedNat_div_eq_packedRatio N
    _ ≤ _ := hpacked

end SymmetricSubgroupAsymptotics.BinaryS16PositiveResidualEstimate
