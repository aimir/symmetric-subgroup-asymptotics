import SymmetricSubgroupAsymptotics.Non2PreE7NonPairPhysicalFrontier
import SymmetricSubgroupAsymptotics.FusionCarrierIncidence
import SymmetricSubgroupAsymptotics.GrowingMenuMassCertificate

/-!
# Numerical closure of the non-pair pre-E7 frontier

This is the owner-or-retained-cell transfer on the exact complement left
after both pair menus have been removed.  Owned axes retain coefficient one;
unowned axes charge their radical/transgression flag and Yoneda fibre jointly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-- Local owner-or-retained-cell bound on one genuinely non-pair action and
literal normal axis. -/
theorem preE7NonPair_survivingEpiCount_le_ownerOrRetainedCells
    {r w b : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (i : PreE7NonPairFirstOwnerIndex (r + 1) w)
    (N : {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    {R : Type*} [Group R] [Finite R]
    (Owned :
      {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → Prop)
    (C : {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ)
    (eta : ℝ)
    (hOwned : ∀ M, Owned M →
      ∀ L : Subgroup (Equiv.Perm (Fin b)),
        fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
            (preE7NonPairFirstOwnerPredicate
              (ownerOrResidualEligible Earlier) w i b) M L ≤
          completeQuotientWeight (R := R) L)
    (K : ∀ M, FusionAxisCarrier (preE7NonPairFirstOwnerAction w i) M)
    (Accepted : ∀ M,
      Subgroup ((K M).checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ M (L : Subgroup (Equiv.Perm (Fin b)))
        (γ : GroupEpimorphism L (K M).checked.quotient),
      (K M).checked.carrierInverseSurvival (K M).source_eq
          (preE7NonPairFirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b)
          (fusionQuotientGraph (K M).checked.beta L γ.1) →
        Accepted M (fusionQuotientGraph (K M).checked.beta L γ.1))
    (Flag : ∀ (_M :
        {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal})
      (_L : Subgroup (Equiv.Perm (Fin b))), Type*)
    (hFlag : ∀ M L, Finite (Flag M L))
    (cell : ∀ M (L : Subgroup (Equiv.Perm (Fin b))),
      FusionCarrierAcceptedEpi (K M).checked L (Accepted M) →
        CompleteQuotientMap L R × Flag M L)
    (Z : ∀ (_M :
        {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal})
      (_L : Subgroup (Equiv.Perm (Fin b))), ℕ)
    (hcell : ∀ M (L : Subgroup (Equiv.Perm (Fin b)))
        (d : CompleteQuotientMap L R × Flag M L),
      Nat.card {γ : FusionCarrierAcceptedEpi (K M).checked L (Accepted M) //
        cell M L γ = d} ≤ Z M L)
    (hcapacity : ∀ M, ¬ Owned M →
      ∀ L : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (Flag M L) * Z M L : ℕ) ≤
          C M * (2 : ℝ) ^ (eta * b)) :
    fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
        (preE7NonPairFirstOwnerPredicate
          (ownerOrResidualEligible Earlier) w i b) N J ≤
      (fusionOwnerCapacityCoefficient b
          (preE7NonPairFirstOwnerAction w i) Owned C eta N *
        (2 : ℝ) ^ (eta * b)) * completeQuotientWeight (R := R) J := by
  apply fusionSurvivingEpiCount_le_ownerCapacityEnvelope_of_ownedBound
    (preE7NonPairFirstOwnerAction w i)
    (preE7NonPairFirstOwnerPredicate
      (ownerOrResidualEligible Earlier) w i b)
    Owned C eta hOwned
  intro M hM L
  letI : Finite (Flag M L) := hFlag M L
  exact (K M).survivingEpiCount_le_of_retainedCells L (Accepted M)
    (haccept M L) (cell M L) (Z M L) (hcell M L)
    (C M) eta (hcapacity M hM L)

/-- Complete numerical closure on the exact non-pair residual. -/
noncomputable def
    preE7NonPair_exponentialForwardEstimate_of_axisOwnerOrRetainedCells
    {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    {ρ : ℝ}
    (R : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
    (Owned : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
      {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → Prop)
    (C : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) (_b : ℕ),
      {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal} → ℝ)
    (A : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ)
    (v : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ)
    (η δ c α : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℝ)
    (ρR : ∀ w i, R w i →* Equiv.Perm (Fin (v w i)))
    (hρR : ∀ w i, Function.Injective (ρR w i))
    (hC : ∀ w i b N, 0 ≤ C w i b N)
    (hA : ∀ w i, A w i =
      (Nat.card (Subgroup.normalizer
        (preE7NonPairFirstOwnerAction w i :
          Set (Equiv.Perm (Fin w)))) : ℝ))
    (hα : ∀ w i, α w i = η w i + c w i)
    (hOwned : ∀ w i b N, Owned w i b N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
            (preE7NonPairFirstOwnerPredicate
              (ownerOrResidualEligible Earlier) w i b) N J ≤
          completeQuotientWeight (R := R w i) J)
    (K : ∀ w i N,
      FusionAxisCarrier (preE7NonPairFirstOwnerAction w i) N)
    (Accepted : ∀ w i b N,
      Subgroup ((K w i N).checked.carrier × Equiv.Perm (Fin b)) → Prop)
    (haccept : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b)))
        (γ : GroupEpimorphism J (K w i N).checked.quotient),
      (K w i N).checked.carrierInverseSurvival (K w i N).source_eq
          (preE7NonPairFirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w i b)
          (fusionQuotientGraph (K w i N).checked.beta J γ.1) →
        Accepted w i b N
          (fusionQuotientGraph (K w i N).checked.beta J γ.1))
    (Flag : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) b
      (_N : {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal})
      (_J : Subgroup (Equiv.Perm (Fin b))), Type*)
    (hFlag : ∀ w i b N J, Finite (Flag w i b N J))
    (cell : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b))),
      FusionCarrierAcceptedEpi (K w i N).checked J (Accepted w i b N) →
        CompleteQuotientMap J (R w i) × Flag w i b N J)
    (Z : ∀ w (i : PreE7NonPairFirstOwnerIndex (r + 1) w) b
      (_N : {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal})
      (_J : Subgroup (Equiv.Perm (Fin b))), ℕ)
    (hcell : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b)))
        (d : CompleteQuotientMap J (R w i) × Flag w i b N J),
      Nat.card {γ : FusionCarrierAcceptedEpi
          (K w i N).checked J (Accepted w i b N) //
        cell w i b N J γ = d} ≤ Z w i b N J)
    (hcapacity : ∀ w i b N, ¬ Owned w i b N →
      ∀ J : Subgroup (Equiv.Perm (Fin b)),
        (Nat.card (Flag w i b N J) * Z w i b N J : ℕ) ≤
          C w i b N * (2 : ℝ) ^ (η w i * b))
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : PolynomialSubquadraticMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (preE7NonPairFirstOwnerAction w i)
        (fusionOwnerCapacityCoefficient b
          (preE7NonPairFirstOwnerAction w i)
          (Owned w i b) (C w i b) (η w i))) A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio := by
  let D : ∀ w, PreE7NonPairFirstOwnerIndex (r + 1) w → ℕ → ℝ :=
    fun w i b => fusionAxisEnvelopeTotal
      (preE7NonPairFirstOwnerAction w i)
      (fusionOwnerCapacityCoefficient b
        (preE7NonPairFirstOwnerAction w i)
        (Owned w i b) (C w i b) (η w i))
  have hmass' : GrowingMenuMassBound 3 D A :=
    growingMenuMassBound_of_polynomialSubquadratic (by omega) D A hmass
  apply preE7NonPair_exponentialForwardEstimate_of_ownerOrResidualAxes
    Earlier hEarlier R
    (fun w i b N => fusionOwnerCapacityCoefficient b
      (preE7NonPairFirstOwnerAction w i)
      (Owned w i b) (C w i b) (η w i) N)
    A v η δ c α ρR hρR
  · intro w i b N
    exact fusionOwnerCapacityCoefficient_nonneg
      (preE7NonPairFirstOwnerAction w i)
      (Owned w i b) (C w i b) (η w i) (hC w i b) N
  · exact hA
  · exact hα
  · intro w i b N J
    exact preE7NonPair_survivingEpiCount_le_ownerOrRetainedCells
      Earlier i N J (Owned w i b) (C w i b) (η w i)
      (hOwned w i b) (K w i) (Accepted w i b) (haccept w i b)
      (Flag w i b) (hFlag w i b) (cell w i b) (Z w i b)
      (hcell w i b) (hcapacity w i b)
  · exact hρ
  · exact hρ8
  · exact hp
  · exact hmass'
  · exact hcoarse

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
