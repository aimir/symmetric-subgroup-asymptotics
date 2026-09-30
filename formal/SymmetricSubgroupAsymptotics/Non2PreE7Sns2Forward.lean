import SymmetricSubgroupAsymptotics.Non2PreE7Sns2HotScalar

/-!
# Complete all-width SNS2 forward estimate

The normalized cold continuation and the correlated hot scalar are combined
only after each has been summed over the same literal SNS2 action menu.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The complete SNS2 contribution is exponentially contractive. -/
noncomputable def preE7Sns2Secondary_exponentialForwardEstimate
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hmass : PreE7Sns2NormalizedMenuMassBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError 5
        (fun w i => preE7Sns2MenuCoefficient (w := w) i)
        (fun w i => preE7Sns2MenuExceptional (w := w) i)
        (fun w i => preE7Sns2MenuNormalizer (w := w) i)
        (fun w i => preE7Sns2MenuSlope (w := w) i)) := by
  let Ecold := preE7Sns2Cold_exponentialForwardEstimate hmass
  let Ehot := (preE7Sns2Hot_exponentialScalarBound hcoarse hmass).toForwardEstimate
  change OrdinaryFrontierClosure.ExponentialForwardEstimate (fun n =>
    (∑ b ∈ Finset.range n,
      growingQuotientColdRow 5
        (fun w i => preE7Sns2MenuCoefficient (w := w) i)
        (fun w i => preE7Sns2MenuNormalizer (w := w) i)
        (fun w i => preE7Sns2MenuSlope (w := w) i) n b *
          ordinarySubgroupRatio b) +
      growingQuotientExceptionalTotal 5
        (fun w i => preE7Sns2MenuExceptional (w := w) i) n)
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.add Ecold Ehot

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
