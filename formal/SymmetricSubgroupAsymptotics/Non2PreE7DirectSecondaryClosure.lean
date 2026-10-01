import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3ExceptionalInterface
import SymmetricSubgroupAsymptotics.GrowingQuotientSecondaryForwardEstimate

/-!
# Direct secondary closure for the final pre-E7 catalogue

The ordinary catalogue can prove its additive cold menu and bounded-support
exceptional scalar separately.  The SNS2 binary-rank-tail row cannot: its
quarter-square cost is paid only after the cold and hot parts have been
summed over the same literal action menu.  This file exposes the already
proved direct-secondary transfer at the exact pre-`E7` interface.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Numerical data for a mixed cover whose complete secondary contribution
has been estimated directly.  This is strictly more general than
`PreE7NoPairNoC3LocalExceptionalNumericalCertificate`: ordinary catalogues
recover it by adding their cold-tail and exceptional estimates, while SNS2
uses its correlated all-width theorem. -/
structure PreE7NoPairNoC3DirectSecondaryNumericalCertificate {r : ℕ}
    (D : PreE7NoPairNoC3LocalExceptionalData r) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_le_eighth : rho ≤ 1 / 8
  parameters : GrowingQuotientParameterBound rho
    D.v D.eta D.delta D.cutoff D.alpha
  main_menu : GrowingMenuMassBound 3 D.D D.A
  secondary : OrdinaryFrontierClosure.ExponentialForwardEstimate
    (growingQuotientSecondaryError 3 D.T D.X D.A D.theta)

/-- The old split numerical certificate canonically gives the direct
secondary certificate. -/
noncomputable def
    PreE7NoPairNoC3LocalExceptionalNumericalCertificate.toDirectSecondary
    {r : ℕ} {D : PreE7NoPairNoC3LocalExceptionalData r}
    (N : PreE7NoPairNoC3LocalExceptionalNumericalCertificate D) :
    PreE7NoPairNoC3DirectSecondaryNumericalCertificate D where
  rho := N.rho
  rho_pos := N.rho_pos
  rho_le_eighth := N.rho_le_eighth
  parameters := N.parameters
  main_menu := N.main_menu
  secondary := by
    let tailError : ℕ → ℝ := fun n =>
      ∑ b ∈ Finset.range n,
        growingQuotientColdRow 3 D.T D.A D.theta n b *
          ordinarySubgroupRatio b
    have htailPhysical : GrowingColdOnlyPhysicalBound
        tailError 3 D.T D.A D.theta :=
      Filter.Eventually.of_forall (fun _ => le_rfl)
    let Ecold := growingColdOnly_exponentialForwardEstimate
      tailError 3 D.T D.A D.theta N.rho_pos N.rho_le_eighth (by omega)
        D.T_nonneg D.A_pos N.tail_gap N.tail_menu htailPhysical
    let Eexceptional := N.exceptional.toForwardEstimate
    simpa only [growingQuotientSecondaryError, tailError] using
      OrdinaryFrontierClosure.ExponentialForwardEstimate.add
        Ecold Eexceptional

/-- A direct estimate of the complete secondary row closes the final
pre-`E7` residual without imposing separate pointwise hypotheses on it. -/
noncomputable def
    preE7NoPairNoC3_exponentialForwardEstimate_of_directSecondaryData
    {r : ℕ} (D : PreE7NoPairNoC3LocalExceptionalData r)
    (N : PreE7NoPairNoC3DirectSecondaryNumericalCertificate D)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio :=
  growingQuotientAdditiveExceptional_exponentialForwardEstimate_of_secondary
    preE7NoPairNoC3ResidualRatio 3 D.D D.T D.X D.A D.v D.eta D.delta
      D.cutoff D.alpha D.theta N.rho_pos N.rho_le_eighth (by omega)
      D.D_nonneg D.A_pos N.parameters N.main_menu hcoarse N.secondary
      D.physical_bound

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
