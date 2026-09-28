import SymmetricSubgroupAsymptotics.FusionQuotientComparator
import SymmetricSubgroupAsymptotics.Non2OwnerAxisFrontier

/-!
# Exact owner-or-capacity envelopes on literal normal axes

Some original normal axes are accepted by an earlier quotient owner, while
the remaining axes must be bounded by the retained-annihilator capacity
argument.  This file combines those alternatives without weakening the
earlier-owner contribution: an owned axis has coefficient exactly one before
the common exponential lift is extracted.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- After extracting the common factor `2^(eta*b)`, an owned quotient axis
has coefficient `2^(-eta*b)`, so its actual contribution remains exactly
one.  An unowned axis retains its supplied capacity coefficient. -/
def fusionOwnerCapacityCoefficient {w : ℕ} (b : ℕ)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Owned : {N : Subgroup U // N.Normal} → Prop)
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (eta : ℝ) (N : {N : Subgroup U // N.Normal}) : ℝ :=
  if Owned N then (2 : ℝ) ^ (-(eta * b)) else C N

theorem fusionOwnerCapacityCoefficient_nonneg {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (Owned : {N : Subgroup U // N.Normal} → Prop)
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (eta : ℝ) (hC : ∀ N, 0 ≤ C N) (N) :
    0 ≤ fusionOwnerCapacityCoefficient b U Owned C eta N := by
  by_cases hN : Owned N
  · simp only [fusionOwnerCapacityCoefficient, if_pos hN]
    exact Real.rpow_nonneg (by norm_num) _
  · simpa only [fusionOwnerCapacityCoefficient, if_neg hN] using hC N

/-- The exact local dichotomy.  An owned axis is injected into one literal
quotient summand of the comparator.  Only an unowned axis invokes the
capacity estimate. -/
theorem fusionSurvivingEpiCount_le_ownerCapacityEnvelope
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    {R : Type*} [Group R] [Finite R]
    (Owned : {N : Subgroup U // N.Normal} → Prop)
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (eta : ℝ)
    (hOwned : ∀ N, Owned N → FusionQuotientComparator U N R)
    (hCapacity : ∀ N, ¬ Owned N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        fusionSurvivingEpiCount U P N J ≤
          (C N * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J)
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      (fusionOwnerCapacityCoefficient b U Owned C eta N *
          (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  by_cases hN : Owned N
  · have hcompare :=
      fusionSurvivingEpiCount_le_completeQuotientWeight_of_comparator
        U P N (hOwned N hN) J
    have hcancel :
        (2 : ℝ) ^ (-(eta * b)) * (2 : ℝ) ^ (eta * b) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring_nf
      norm_num
    simpa only [fusionOwnerCapacityCoefficient, if_pos hN, hcancel,
      one_mul] using hcompare
  · simpa only [fusionOwnerCapacityCoefficient, if_neg hN] using
      hCapacity N hN J

/-- Summing the dichotomy over the literal normal axes keeps coefficient one
on every earlier-owned axis and sums only the supplied coefficients on the
unowned axes. -/
theorem fusionCompleteSourceSum_le_ownerCapacityEnvelope
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    {R : Type*} [Group R] [Finite R]
    (Owned : {N : Subgroup U // N.Normal} → Prop)
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (eta : ℝ)
    (hOwned : ∀ N, Owned N → FusionQuotientComparator U N R)
    (hCapacity : ∀ N, ¬ Owned N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        fusionSurvivingEpiCount U P N J ≤
          (C N * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum U P J ≤
      (fusionAxisEnvelopeTotal U
      (fusionOwnerCapacityCoefficient b U Owned C eta) *
          (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  exact fusionCompleteSourceSum_le_axisEnvelopeTotal_rpow U P
    (fusionOwnerCapacityCoefficient b U Owned C eta)
    (fun K => completeQuotientWeight (R := R) K) eta
    (fusionSurvivingEpiCount_le_ownerCapacityEnvelope
      U P Owned C eta hOwned hCapacity) J

namespace RepeatedMarkerOwnerBound

/-- Full non-2 forward estimate from the literal owner-or-capacity
dichotomy.  Comparator-owned axes are discharged automatically with exact
coefficient one.  The caller supplies a retained-annihilator estimate only
for axes rejected by the chosen earlier quotient owner. -/
noncomputable def
    outsideFrontier_exponentialForwardEstimate_of_axisOwnerOrCapacity
    {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    {ρ : ℝ}
    (R : ∀ w, Non2FirstOwnerIndex (r+1) w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
    (Owned : ∀ w (i : Non2FirstOwnerIndex (r+1) w) (_b : ℕ),
      {N : Subgroup (non2FirstOwnerAction w i) // N.Normal} → Prop)
    (C : ∀ w (i : Non2FirstOwnerIndex (r+1) w) (_b : ℕ),
      {N : Subgroup (non2FirstOwnerAction w i) // N.Normal} → ℝ)
    (A : ∀ w, Non2FirstOwnerIndex (r+1) w → ℝ)
    (v : ∀ w, Non2FirstOwnerIndex (r+1) w → ℕ)
    (η δ c α : ∀ w, Non2FirstOwnerIndex (r+1) w → ℝ)
    (ρR : ∀ w i, R w i →* Equiv.Perm (Fin (v w i)))
    (hρR : ∀ w i, Function.Injective (ρR w i))
    (hC : ∀ w i b N, 0 ≤ C w i b N)
    (hA : ∀ w i, A w i =
      (Nat.card (Subgroup.normalizer
        (non2FirstOwnerAction w i : Set (Equiv.Perm (Fin w)))) : ℝ))
    (hα : ∀ w i, α w i = η w i + c w i)
    (hOwned : ∀ w i b N, Owned w i b N →
      FusionQuotientComparator
        (non2FirstOwnerAction w i) N (R w i))
    (hCapacity : ∀ w i b N, ¬ Owned w i b N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        fusionSurvivingEpiCount (non2FirstOwnerAction w i)
            (non2FirstOwnerPredicate
              (ownerOrResidualEligible Earlier) w i b) N J ≤
          (C w i b N * (2 : ℝ) ^ (η w i * b)) *
            completeQuotientWeight (R := R w i) J)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (non2FirstOwnerAction w i)
        (fusionOwnerCapacityCoefficient b
          (non2FirstOwnerAction w i) (Owned w i b) (C w i b) (η w i))) A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      OrdinaryFrontierClosure.outsideFrontierRatio := by
  exact outsideFrontier_exponentialForwardEstimate_of_ownerOrResidualAxes
    Earlier hEarlier R
    (fun w i b N => fusionOwnerCapacityCoefficient b
      (non2FirstOwnerAction w i) (Owned w i b) (C w i b) (η w i) N)
    A v η δ c α ρR hρR
    (fun w i b N => fusionOwnerCapacityCoefficient_nonneg
      (b := b)
      (non2FirstOwnerAction w i) (Owned w i b) (C w i b) (η w i)
      (hC w i b) N)
    hA hα
    (fun w i b N J =>
      fusionSurvivingEpiCount_le_ownerCapacityEnvelope
        (non2FirstOwnerAction w i)
        (non2FirstOwnerPredicate
          (ownerOrResidualEligible Earlier) w i b)
        (Owned w i b) (C w i b) (η w i)
        (hOwned w i b) (hCapacity w i b) N J)
    hρ hρ8 hp hmass hcoarse

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
