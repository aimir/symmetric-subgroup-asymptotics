import SymmetricSubgroupAsymptotics.PrimeCentralJointElementaryEnvelope
import SymmetricSubgroupAsymptotics.FusionCompleteQuotientPrimeTransfer
import SymmetricSubgroupAsymptotics.RelativeCompleteSourceEnvelope

/-!
# Relative complete-source envelopes with retained prime markers

This is the construction-facing object produced by cutting the invariant
part from one elementary affine layer.  The quotient tower remains an
ordinary relative complete-source envelope, while the fixed part is retained
as literal prime-character columns on the same complete source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A complete-source transfer whose terminal quotient maps and prime
markers share the same source. -/
structure PrimeMarkedRelativeCompleteSourceEnvelope
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G] where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  quotientDegree : ℕ
  action : R →* Equiv.Perm (Fin quotientDegree)
  action_injective : Function.Injective action
  markerColumns : ℕ
  coefficient : ℕ → ℝ
  eta : ℝ
  coefficient_nonneg : ∀ b, 0 ≤ coefficient b
  bound : ∀ b (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := G) J ≤
      coefficient b * (2 : ℝ) ^ (eta * b) *
        completeQuotientPrimeWeight p (R := R) markerColumns J

attribute [instance]
  PrimeMarkedRelativeCompleteSourceEnvelope.groupR
  PrimeMarkedRelativeCompleteSourceEnvelope.finiteR

namespace PrimeMarkedRelativeCompleteSourceEnvelope

theorem jointDegree_pos
    (p : ℕ) [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    (E : PrimeMarkedRelativeCompleteSourceEnvelope p G)
    (hquotient : 0 < E.quotientDegree) :
    0 < E.quotientDegree + p * E.markerColumns := by
  omega

private theorem rpow_eq_two_rpow_logb
    {B : ℝ} (hB : 0 < B) (x : ℝ) :
    B ^ x = (2 : ℝ) ^ (Real.logb 2 B * x) := by
  rw [Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) hB]

/-- Add an elementary layer after cutting its full invariant radical.  The
ordinary quotient-capacity exponent and the retained fixed columns are never
maximized separately in the final moment. -/
noncomputable def elementaryPrimeCutStep
    (p : ℕ) [Fact p.Prime]
    {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
    (π : G →* B) (hπ : Function.Surjective π)
    (A : Rep (ZMod p) B) [Finite A]
    (K : OriginalKernelModuleChart π A)
    (H : PrimeCentralLayerJointCapacityBound p π hπ A K)
    (Q : RelativeCompleteSourceEnvelope B) :
    PrimeMarkedRelativeCompleteSourceEnvelope p G where
  R := Q.R
  groupR := Q.groupR
  finiteR := Q.finiteR
  quotientDegree := Q.v
  action := Q.action
  action_injective := Q.action_injective
  markerColumns := H.fixedCapacity
  coefficient := fun b ↦ H.coefficient * Q.coefficient b
  eta := Real.logb 2 p / p * H.quotientCapacity + Q.eta
  coefficient_nonneg := fun b ↦
    mul_nonneg H.coefficient_nonneg (Q.coefficient_nonneg b)
  bound := by
    intro b J
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (Fact.out : p.Prime).pos
    have hq := Q.bound b J
    have hcut := H.completeQuotientWeight_le_primeCut p π hπ A K J
    have hpow :
        (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) =
          (2 : ℝ) ^
            ((Real.logb 2 p / p * H.quotientCapacity) * (b : ℝ)) := by
      rw [rpow_eq_two_rpow_logb hp0]
      congr 1
      field_simp
    calc
      completeQuotientWeight (R := G) J ≤
          H.coefficient *
            (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) *
            ((p : ℝ) ^ (H.fixedCapacity *
              Module.finrank (ZMod p) (PrimeCharacters p J)) *
              completeQuotientWeight (R := B) J) := hcut
      _ ≤ H.coefficient *
            (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) *
            ((p : ℝ) ^ (H.fixedCapacity *
              Module.finrank (ZMod p) (PrimeCharacters p J)) *
              (Q.coefficient b * (2 : ℝ) ^ (Q.eta * b) *
                completeQuotientWeight (R := Q.R) J)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hq (by positivity))
            (mul_nonneg H.coefficient_nonneg (by positivity))
      _ = (H.coefficient * Q.coefficient b) *
            (2 : ℝ) ^
              ((Real.logb 2 p / p * H.quotientCapacity + Q.eta) * b) *
            completeQuotientPrimeWeight p (R := Q.R)
              H.fixedCapacity J := by
          rw [hpow, show
            (Real.logb 2 p / p * H.quotientCapacity + Q.eta) * (b : ℝ) =
              (Real.logb 2 p / p * H.quotientCapacity) * b +
                Q.eta * b by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          unfold completeQuotientPrimeWeight
          ring

/-- The marked envelope immediately yields the physical prime-moment row
for every natural survival predicate below its complete source. -/
theorem physical_kernel_bound
    (p : ℕ) [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    (E : PrimeMarkedRelativeCompleteSourceEnvelope p G)
    {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (hsource : ∀ J,
      fusionCompleteSourceSum U P J ≤
        completeQuotientWeight (R := G) J)
    (delta cutoff : ℝ) :
    (Nat.card
        (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientHotKernel (fun n ↦ (subgroupCount n : ℝ))
          b w (E.quotientDegree + p * E.markerColumns)
          (E.coefficient b)
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          E.eta delta cutoff +
        fusionWidthColdKernel b w (E.coefficient b)
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin w)))) : ℝ)
          (E.eta + cutoff) * ordinarySubgroupRatio b := by
  apply fusionPhysical_growingQuotientPrime_kernel_bound p
    U P hP E.action E.action_injective
      (E.coefficient b) E.eta delta cutoff
      (E.coefficient_nonneg b)
  intro J
  exact (hsource J).trans (E.bound b J)

end PrimeMarkedRelativeCompleteSourceEnvelope
end SymmetricSubgroupAsymptotics

end
