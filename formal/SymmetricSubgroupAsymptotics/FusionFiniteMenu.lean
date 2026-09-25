import SymmetricSubgroupAsymptotics.FusionPhysicalCount
import SymmetricSubgroupAsymptotics.FusionNumerics

/-!
# Actual finite-menu fusion from local same-source certificates

First apply original-normalizer pointing to the complete natural local
family. Only then split its exact literal-axis/source sum numerically.
Individual axes and hot tests need not be normalizer-fixed. All bounds
below concern actual physical subgroups, not abstract surrogate counts.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Hot/cold summation on one retained source set. The local factor D is
charged once outside the moment; no bounded total subgroup count is assumed. -/
theorem fusion_hot_cold_sum_le {ι : Type*} [Fintype ι]
    (f Φ : ι → ℝ) {D t M : ℝ} (hD : 0≤D) (ht : 0<t)
    (hΦ : ∀ i, 0≤Φ i) (hf : ∀ i, f i≤D*Φ i)
    {q : ℕ} (hq : 1≤q) (hmoment : ∑ i, Φ i^q≤M) :
    (∑ i, f i) ≤ D/t^(q-1)*M + (Nat.card ι : ℝ)*D*t := by
  have hhot := fusion_hot_sum_le f Φ hD ht hΦ hf hq hmoment
  have hcold : (∑ i ∈ Finset.univ.filter (fun i => ¬ t<Φ i), f i) ≤
      (Nat.card ι : ℝ)*D*t := by
    calc
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ t<Φ i), D*t := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : Φ i≤t := le_of_not_gt (Finset.mem_filter.mp hi).2
        exact (hf i).trans (mul_le_mul_of_nonneg_left hi' hD)
      _ ≤ ∑ _i : ι, D*t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact mul_nonneg hD ht.le
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]
        ring
  calc
    _ = (∑ i ∈ Finset.univ.filter (fun i => t<Φ i), f i) +
        ∑ i ∈ Finset.univ.filter (fun i => ¬ t<Φ i), f i :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ _ := add_le_add hhot hcold

variable {Ω Z : Type*} (U : Subgroup (Equiv.Perm Ω))

/-- Literal surviving epi count used in the actual physical sum. -/
def fusionSurvivingEpiCount (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (N : {N : Subgroup U // N.Normal}) (J : Subgroup (Equiv.Perm Z)) : ℝ :=
  Nat.card {β : GroupEpimorphism J (U ⧸ N.1) // P (fusionFullGoursatEncode N J β).1}

/-- A finite-menu theorem on actual subgroup families. The input bounds
are only per-source local quotient envelopes and same-source moments.
The whole-family bound, original divisor, hot summation, and cold source
multiplicity are conclusions. An excluded literal axis may have D=0. -/
theorem fusionPhysical_finite_menu [Fintype Ω] [Fintype Z]
    (P : Subgroup (U × Equiv.Perm Z) → Prop) (hP : FusionOrbitNatural U P)
    (Φ : {N : Subgroup U // N.Normal} → Subgroup (Equiv.Perm Z) → ℝ)
    (D t M : {N : Subgroup U // N.Normal} → ℝ)
    (q : {N : Subgroup U // N.Normal} → ℕ)
    (hD : ∀ N, 0≤D N) (ht : ∀ N, 0<t N)
    (hΦ : ∀ N J, 0≤Φ N J)
    (henvelope : ∀ N J, fusionSurvivingEpiCount U P N J ≤ D N*Φ N J)
    (hq : ∀ N, 1≤q N)
    (hmoment : ∀ N, (∑ J : Subgroup (Equiv.Perm Z), Φ N J^(q N)) ≤ M N) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) ≤
      ((Fintype.card Ω+Fintype.card Z).factorial : ℝ) /
        ((Fintype.card Z).factorial *
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm Ω))) : ℝ)) *
      ∑ N : {N : Subgroup U // N.Normal},
        (D N/(t N)^(q N-1)*M N +
          (Nat.card (Subgroup (Equiv.Perm Z)) : ℝ)*D N*t N) := by
  apply (fusionPhysical_original_weight U P hP).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  push_cast
  apply Finset.sum_le_sum
  intro N _
  exact fusion_hot_cold_sum_le (fusionSurvivingEpiCount U P N) (Φ N)
    (hD N) (ht N) (hΦ N) (henvelope N) (hq N) (hmoment N)

/-- Canonical-degree form: the cold multiplicity is exactly the subgroup
count of the untouched complete complement on b physical points. -/
theorem fusionPhysical_finite_menu_degree {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (b : ℕ) (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (Φ : {N : Subgroup U // N.Normal} → Subgroup (Equiv.Perm (Fin b)) → ℝ)
    (D t M : {N : Subgroup U // N.Normal} → ℝ)
    (q : {N : Subgroup U // N.Normal} → ℕ)
    (hD : ∀ N, 0≤D N) (ht : ∀ N, 0<t N)
    (hΦ : ∀ N J, 0≤Φ N J)
    (henvelope : ∀ N J, fusionSurvivingEpiCount U P N J ≤ D N*Φ N J)
    (hq : ∀ N, 1≤q N)
    (hmoment : ∀ N, (∑ J : Subgroup (Equiv.Perm (Fin b)), Φ N J^(q N)) ≤ M N) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) ≤
      ((w+b).factorial : ℝ) /
        (b.factorial * (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w)))) : ℝ)) *
      ∑ N : {N : Subgroup U // N.Normal},
        (D N/(t N)^(q N-1)*M N + (subgroupCount b : ℝ)*D N*t N) := by
  simpa only [Fintype.card_fin,subgroupCount] using
    fusionPhysical_finite_menu U P hP Φ D t M q hD ht hΦ henvelope hq hmoment

end SymmetricSubgroupAsymptotics
