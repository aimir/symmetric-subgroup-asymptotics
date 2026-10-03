import SymmetricSubgroupAsymptotics.CompleteQuotientPrimeMoment
import SymmetricSubgroupAsymptotics.GrowingQuotientHotKernel
import SymmetricSubgroupAsymptotics.OrdinaryRemainderAssembly

/-!
# Physical transfer for a complete quotient with retained prime markers

The invariant part of an elementary affine layer and the literal quotient
top are correlated through the same complete source.  Their weights must
therefore be split by one joint moment.  This file exposes the corresponding
real-valued weight and installs it in the original-weight physical transfer.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Complete quotient weight with `c` retained prime-character columns on
the same literal source. -/
def completeQuotientPrimeWeight
    (p : ℕ) [Fact p.Prime]
    {R : Type*} [Group R] [Finite R]
    {b : ℕ} (c : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  completeQuotientWeight (R := R) J *
    (p : ℝ) ^ (c * Module.finrank (ZMod p) (PrimeCharacters p J))

theorem completeQuotientPrimeWeight_nonneg
    (p : ℕ) [Fact p.Prime]
    {R : Type*} [Group R] [Finite R]
    {b : ℕ} (c : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    0 ≤ completeQuotientPrimeWeight p (R := R) c J := by
  unfold completeQuotientPrimeWeight
  exact mul_nonneg (completeQuotientWeight_nonneg J)
    (pow_nonneg (Nat.cast_nonneg p) _)

/-- The same-source graph gives the exact real-valued joint moment. -/
theorem completeQuotientPrimeWeight_moment_le_real
    (p : ℕ) [Fact p.Prime]
    {R : Type*} [Group R] [Finite R]
    {s : ℕ} (ρ : R →* Equiv.Perm (Fin s))
    (hρ : Function.Injective ρ) (b c q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        completeQuotientPrimeWeight p (R := R) c J ^ q) ≤
      (subgroupCount (b + q * (s + p * c)) : ℝ) := by
  unfold completeQuotientPrimeWeight completeQuotientWeight
  exact_mod_cast completeQuotientPrimeWeight_moment_le p ρ hρ b c q

/-- Original-weight physical hot/cold transfer for the joint quotient and
prime-marker weight.  The cold multiplicity is still exactly the number of
unchanged complete sources. -/
theorem fusionPhysical_completeQuotientPrime_normalized_bound
    (p : ℕ) [Fact p.Prime]
    {R : Type*} [Group R] [Finite R]
    {w s b c q : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (ρ : R →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (D t : ℝ) (hD : 0 ≤ D) (ht : 0 < t) (hq : 1 ≤ q)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        D * completeQuotientPrimeWeight p (R := R) c J) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ) *
        (D / t ^ (q - 1) *
            (subgroupCount (b + q * (s + p * c)) : ℝ) +
          (subgroupCount b : ℝ) * D * t) := by
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  let point : ℝ := growingQuotientNormalizedPointing b w A
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (U : Set (Equiv.Perm (Fin w)))))
  have hpoint : 0 ≤ point := by
    dsimp [point]
    unfold growingQuotientNormalizedPointing
    exact div_nonneg
      (div_nonneg (div_nonneg (by positivity) (by positivity)) hA.le)
      (exactBenchmark_pos (b + w)).le
  have hsum := fusion_hot_cold_sum_le
    (fusionCompleteSourceSum U P)
    (completeQuotientPrimeWeight p (R := R) c)
    hD ht (completeQuotientPrimeWeight_nonneg p (R := R) c)
    henvelope hq
    (completeQuotientPrimeWeight_moment_le_real p ρ hρ b c q)
  have hphysical := fusionPhysical_original_weight U P hP
  simp only [Fintype.card_fin, Nat.add_comm w b] at hphysical
  have hnormalized :
      (Nat.card
          (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
          exactBenchmark (b + w) ≤
        point *
          (∑ J : Subgroup (Equiv.Perm (Fin b)),
            fusionCompleteSourceSum U P J) := by
    have hbench := exactBenchmark_pos (b + w)
    have hdiv := div_le_div_of_nonneg_right hphysical hbench.le
    convert hdiv using 1
    simp only [fusionCompleteSourceSum, Nat.cast_sum]
    rw [Finset.sum_comm]
    unfold fusionSurvivingEpiCount
    dsimp [point, growingQuotientNormalizedPointing, A]
    ring
  exact hnormalized.trans (mul_le_mul_of_nonneg_left hsum hpoint)

/-- Kernel form.  The graph degree is the faithful quotient degree plus the
literal `p*c` marker degree; no independent maximization is used. -/
theorem fusionPhysical_growingQuotientPrime_kernel_bound
    (p : ℕ) [Fact p.Prime]
    {R : Type*} [Group R] [Finite R]
    {w s b c : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (ρ : R →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (D eta delta cutoff : ℝ) (hD : 0 ≤ D)
    (henvelope : ∀ J,
      fusionCompleteSourceSum U P J ≤
        (D * (2 : ℝ) ^ (eta * b)) *
          completeQuotientPrimeWeight p (R := R) c J) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n ↦ (subgroupCount n : ℝ))
          b w (s + p * c) D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          eta delta cutoff +
        fusionWidthColdKernel b w D
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          (eta + cutoff) * ordinarySubgroupRatio b := by
  let v := s + p * c
  let q := growingQuotientMoment delta (v : ℝ) (b : ℝ)
  let A : ℝ := Nat.card
    (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w))))
  have hq : 1 ≤ q := growingQuotientMoment_pos delta (v : ℝ) (b : ℝ)
  have hfactor : 0 ≤ D * (2 : ℝ) ^ (eta * b) :=
    mul_nonneg hD (by positivity)
  have ht := growingQuotientThreshold_pos cutoff b
  have hbound := fusionPhysical_completeQuotientPrime_normalized_bound
    p U P hP ρ hρ (D * (2 : ℝ) ^ (eta * b))
      (growingQuotientThreshold cutoff b) hfactor ht hq henvelope
  change _ ≤
    growingQuotientHotKernel (fun n ↦ (subgroupCount n : ℝ))
        b w v D A eta delta cutoff +
      fusionWidthColdKernel b w D A (eta + cutoff) *
        ordinarySubgroupRatio b
  calc
    _ ≤ growingQuotientNormalizedPointing b w A *
        (D * (2 : ℝ) ^ (eta * b) /
            growingQuotientThreshold cutoff b ^ (q - 1) *
              (subgroupCount (b + q * v) : ℝ) +
          (subgroupCount b : ℝ) * D * (2 : ℝ) ^ (eta * b) *
            growingQuotientThreshold cutoff b) := by
      simpa only [q, v, A, growingQuotientNormalizedPointing,
        div_eq_mul_inv, mul_assoc] using hbound
    _ = growingQuotientNormalizedPointing b w A *
          (D * (2 : ℝ) ^ (eta * b) /
              growingQuotientThreshold cutoff b ^ (q - 1) *
                (subgroupCount (b + q * v) : ℝ)) +
        growingQuotientNormalizedPointing b w A *
          ((subgroupCount b : ℝ) * D * (2 : ℝ) ^ (eta * b) *
            growingQuotientThreshold cutoff b) := by ring
    _ = _ := by
      congr 1
      · simpa only [q, growingQuotientGraphDegree] using
          growingQuotient_hot_identity
            (fun n ↦ (subgroupCount n : ℝ)) b w v D A eta delta cutoff
      · exact growingQuotient_cold_identity (subgroupCount b : ℝ)
          b w D A eta cutoff

end SymmetricSubgroupAsymptotics

end
