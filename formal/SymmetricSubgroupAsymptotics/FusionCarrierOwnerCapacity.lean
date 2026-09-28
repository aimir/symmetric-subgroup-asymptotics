import SymmetricSubgroupAsymptotics.BinaryCarrierEpiSurvival
import SymmetricSubgroupAsymptotics.FusionOwnerCapacityEnvelope

/-!
# Reversible carriers for the owner-or-capacity envelope

An unowned original normal axis may be bounded after transporting it through
a checked permutation carrier.  The carrier remembers the literal original
source and normal axis, while `carrierInverseSurvival` tests acceptance on the
inverse reconstructed original subgroup.  Consequently the exterior subgroup
`J`, every preceding first-owner exclusion, and the original quotient-map
multiplicity are unchanged.

This file is the interface between intrinsic carrier counts and the reusable
general non-2 owner-or-capacity theorem.  It does not assume that a carrier is
accepted by an earlier owner and it does not replace the intrinsic carrier
envelope by a structural state description.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A checked reversible carrier attached to one literal normal axis of the
original permutation action.  The carrier degree may depend on the axis. -/
structure FusionAxisCarrier {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (N : {N : Subgroup U // N.Normal}) where
  degree : ℕ
  checked : CheckedPermutationCarrier w degree
  source_eq : checked.source = U
  axis_eq : checked.axis = N.1.map U.subtype

namespace FusionAxisCarrier

/-- An intrinsic carrier bound returns to the exact original surviving-epi
count.  In particular, the same complete exterior source `J` occurs on both
sides and survival is checked after inverse reconstruction of the original
subgroup. -/
theorem survivingEpiCount_le_of_intrinsic
    {w b : ℕ}
    {U : Subgroup (Equiv.Perm (Fin w))}
    {P : Subgroup (U × Equiv.Perm (Fin b)) → Prop}
    {N : {N : Subgroup U // N.Normal}}
    (K : FusionAxisCarrier U N)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (Accepted : Subgroup (K.checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ δ : GroupEpimorphism J K.checked.quotient,
      K.checked.carrierInverseSurvival K.source_eq P
          (fusionQuotientGraph K.checked.beta J δ.1) →
        Accepted (fusionQuotientGraph K.checked.beta J δ.1))
    (B : ℝ)
    (henvelope :
      (Nat.card {δ : GroupEpimorphism J K.checked.quotient //
        Accepted (fusionQuotientGraph K.checked.beta J δ.1)} : ℝ) ≤ B) :
    fusionSurvivingEpiCount U P N J ≤ B := by
  exact K.checked.originalSurvivingEpiCount_le_of_carrier_envelope
    K.source_eq P N K.axis_eq J Accepted haccept B henvelope

/-- Checked carriers discharge precisely the unowned-axis premise of the
owner-or-capacity theorem.  Earlier-owned axes retain coefficient one; only
an unowned axis invokes its intrinsic carrier envelope. -/
theorem survivingEpiCount_le_ownerCapacity_of_intrinsic
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    {R : Type*} [Group R] [Finite R]
    (Owned : {N : Subgroup U // N.Normal} → Prop)
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (eta : ℝ)
    (hOwned : ∀ N, Owned N → FusionQuotientComparator U N R)
    (K : ∀ N, FusionAxisCarrier U N)
    (Accepted : ∀ N,
      Subgroup ((K N).checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ N (J : Subgroup (Equiv.Perm (Fin b)))
        (δ : GroupEpimorphism J (K N).checked.quotient),
      (K N).checked.carrierInverseSurvival (K N).source_eq P
          (fusionQuotientGraph (K N).checked.beta J δ.1) →
        Accepted N (fusionQuotientGraph (K N).checked.beta J δ.1))
    (henvelope : ∀ N, ¬ Owned N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card {δ : GroupEpimorphism J (K N).checked.quotient //
          Accepted N (fusionQuotientGraph (K N).checked.beta J δ.1)} : ℝ) ≤
          (C N * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J)
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      (fusionOwnerCapacityCoefficient b U Owned C eta N *
          (2 : ℝ) ^ (eta * b)) *
        completeQuotientWeight (R := R) J := by
  apply fusionSurvivingEpiCount_le_ownerCapacityEnvelope
    U P Owned C eta hOwned
  intro M hM L
  exact (K M).survivingEpiCount_le_of_intrinsic L (Accepted M)
    (haccept M L) _ (henvelope M hM L)

/-- Summing the reversible carrier dichotomy retains every literal original
normal axis and changes neither the complete source nor its quotient moment. -/
theorem completeSourceSum_le_ownerCapacity_of_intrinsic
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    {R : Type*} [Group R] [Finite R]
    (Owned : {N : Subgroup U // N.Normal} → Prop)
    (C : {N : Subgroup U // N.Normal} → ℝ)
    (eta : ℝ)
    (hOwned : ∀ N, Owned N → FusionQuotientComparator U N R)
    (K : ∀ N, FusionAxisCarrier U N)
    (Accepted : ∀ N,
      Subgroup ((K N).checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ N (J : Subgroup (Equiv.Perm (Fin b)))
        (δ : GroupEpimorphism J (K N).checked.quotient),
      (K N).checked.carrierInverseSurvival (K N).source_eq P
          (fusionQuotientGraph (K N).checked.beta J δ.1) →
        Accepted N (fusionQuotientGraph (K N).checked.beta J δ.1))
    (henvelope : ∀ N, ¬ Owned N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card {δ : GroupEpimorphism J (K N).checked.quotient //
          Accepted N (fusionQuotientGraph (K N).checked.beta J δ.1)} : ℝ) ≤
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
    (fun L => completeQuotientWeight (R := R) L) eta
    (survivingEpiCount_le_ownerCapacity_of_intrinsic
      U P Owned C eta hOwned K Accepted haccept henvelope) J

end FusionAxisCarrier

namespace RepeatedMarkerOwnerBound

/-- Full general non-2 forward estimate from earlier quotient owners and
intrinsic reversible-carrier envelopes on the rejected axes.  This is the
global form of `FusionAxisCarrier.survivingEpiCount_le_of_intrinsic`: the
carrier step is performed before the literal axes are summed and before the
complete quotient moment is applied. -/
noncomputable def
    outsideFrontier_exponentialForwardEstimate_of_axisOwnerOrCarrier
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
    (K : ∀ w i N,
      FusionAxisCarrier (non2FirstOwnerAction w i) N)
    (Accepted : ∀ w i b N,
      Subgroup ((K w i N).checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b)))
        (γ : GroupEpimorphism J (K w i N).checked.quotient),
      (K w i N).checked.carrierInverseSurvival
          (K w i N).source_eq
          (non2FirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b)
          (fusionQuotientGraph (K w i N).checked.beta J γ.1) →
        Accepted w i b N
          (fusionQuotientGraph (K w i N).checked.beta J γ.1))
    (henvelope : ∀ w i b N, ¬ Owned w i b N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card {γ : GroupEpimorphism J (K w i N).checked.quotient //
          Accepted w i b N
            (fusionQuotientGraph (K w i N).checked.beta J γ.1)} : ℝ) ≤
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
  apply outsideFrontier_exponentialForwardEstimate_of_axisOwnerOrCapacity
    Earlier hEarlier R Owned C A v η δ c α ρR hρR hC hA hα hOwned
  · intro w i b N hN J
    exact (K w i N).survivingEpiCount_le_of_intrinsic J
      (Accepted w i b N) (haccept w i b N J) _
      (henvelope w i b N hN J)
  · exact hρ
  · exact hρ8
  · exact hp
  · exact hmass
  · exact hcoarse

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
