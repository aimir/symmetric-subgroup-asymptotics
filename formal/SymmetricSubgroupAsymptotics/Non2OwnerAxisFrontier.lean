import SymmetricSubgroupAsymptotics.Non2OwnerCapacityFrontier
import SymmetricSubgroupAsymptotics.FusionCompleteSourceEnvelope

/-!
# Normal-axis endgame for the owner-or-capacity frontier

This is the narrow theorem consumed by the remaining incidence argument.
For each first-owner/action label and literal normal axis, prove one surviving
epimorphism envelope on the unchanged complete source.  The theorem sums the
axes, applies the complete quotient moment, and returns the full outside
frontier forward estimate.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace RepeatedMarkerOwnerBound

noncomputable def
    outsideFrontier_exponentialForwardEstimate_of_ownerOrResidualAxes
    {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hEarlier : DegreeNaturalOwnerMenu Earlier)
    { ρ : ℝ }
    (R : ∀ w, Non2FirstOwnerIndex (r+1) w → Type*)
    [∀ w i, Group (R w i)] [∀ w i, Finite (R w i)]
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
    (haxis : ∀ w i b N (J : Subgroup (Equiv.Perm (Fin b))),
      fusionSurvivingEpiCount (non2FirstOwnerAction w i)
          (non2FirstOwnerPredicate (ownerOrResidualEligible Earlier) w i b)
          N J ≤
        (C w i b N * (2 : ℝ) ^ (η w i * b)) *
          completeQuotientWeight (R := R w i) J)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hp : GrowingQuotientParameterBound ρ v η δ c α)
    (hmass : GrowingMenuMassBound 3
      (fun w i b => fusionAxisEnvelopeTotal
        (non2FirstOwnerAction w i) (C w i b)) A)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      OrdinaryFrontierClosure.outsideFrontierRatio := by
  let D : ∀ w, Non2FirstOwnerIndex (r+1) w → ℕ → ℝ :=
    fun w i b => fusionAxisEnvelopeTotal
      (non2FirstOwnerAction w i) (C w i b)
  have hD : ∀ w i b, 0 ≤ D w i b := by
    intro w i b
    exact fusionAxisEnvelopeTotal_nonneg
      (non2FirstOwnerAction w i) (C w i b) (hC w i b)
  have henvelope : ∀ w i b (J : Subgroup (Equiv.Perm (Fin b))),
      fusionCompleteSourceSum (non2FirstOwnerAction w i)
          (non2FirstOwnerPredicate (ownerOrResidualEligible Earlier) w i b) J ≤
        (D w i b * (2 : ℝ) ^ (η w i * b)) *
          completeQuotientWeight (R := R w i) J := by
    intro w i b J
    exact fusionCompleteSourceSum_le_axisEnvelopeTotal_rpow
      (non2FirstOwnerAction w i)
      (non2FirstOwnerPredicate (ownerOrResidualEligible Earlier) w i b)
      (C w i b) (fun K => completeQuotientWeight (R := R w i) K)
      (η w i) (haxis w i b) J
  exact outsideFrontier_exponentialForwardEstimate_of_ownerOrResidual
    Earlier hEarlier R D A v η δ c α ρR hρR hD hA hα henvelope
      hρ hρ8 hp hmass hcoarse

end RepeatedMarkerOwnerBound
end SymmetricSubgroupAsymptotics

end
