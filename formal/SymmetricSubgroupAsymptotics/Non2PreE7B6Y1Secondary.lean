import SymmetricSubgroupAsymptotics.Non2PreE7B6Y1Menu
import SymmetricSubgroupAsymptotics.GrowingQuotientSecondaryForwardEstimate

/-!
# Complete fixed-width B6 and Y1 secondary estimates

The cold continuation and correlated hot scalar of each rank-tail family are
combined only after summing its complete literal action menu.  No uniform
bound on the action-dependent certificate constants is assumed.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The complete B6 cold-plus-hot contribution is exponentially
contractive. -/
noncomputable def preE7B6Secondary_exponentialForwardEstimate
    (lit : PreE7CharacterLiterature)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError 3
        (fun w i => preE7B6MenuCoefficient lit (w := w) i)
        (fun w i => preE7B6MenuExceptional lit (w := w) i)
        (fun w i => preE7B6MenuNormalizer (w := w) i)
        (fun _ _ => (4 / 3 : ℝ))) := by
  let coldError : ℕ → ℝ := fun n =>
    ∑ b ∈ Finset.range n,
      growingQuotientColdRow 3
        (fun w i => preE7B6MenuCoefficient lit (w := w) i)
        (fun w i => preE7B6MenuNormalizer (w := w) i)
        (fun _ _ => (4 / 3 : ℝ)) n b * ordinarySubgroupRatio b
  let Ecold := growingColdOnly_exponentialForwardEstimate coldError
    3
    (fun w i => preE7B6MenuCoefficient lit (w := w) i)
    (fun w i => preE7B6MenuNormalizer (w := w) i)
    (fun _ _ => (4 / 3 : ℝ))
    (by norm_num [preE7CharacterRho])
    (by norm_num [preE7CharacterRho]) (by omega)
    (fun _ i b => preE7B6MenuCoefficient_nonneg lit i b)
    (fun _ i => preE7B6MenuNormalizer_pos i)
    (fun _ i => (preE7B6MenuCertificate lit i).cold_gap)
    (preE7B6MenuMass lit)
    (Filter.Eventually.of_forall (fun _ => le_rfl))
  let Ehot := (preE7B6MenuExceptionalBound lit hcoarse).toForwardEstimate
  simpa only [growingQuotientSecondaryError, coldError] using
    OrdinaryFrontierClosure.ExponentialForwardEstimate.add Ecold Ehot

/-- The complete Y1 cold-plus-hot contribution is exponentially
contractive. -/
noncomputable def preE7Y1Secondary_exponentialForwardEstimate
    (lit : PreE7CharacterLiterature)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (growingQuotientSecondaryError 3
        (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
        (fun w i => preE7Y1MenuExceptional lit (w := w) i)
        (fun w i => preE7Y1MenuNormalizer (w := w) i)
        (fun _ _ => (153 / 200 : ℝ))) := by
  let coldError : ℕ → ℝ := fun n =>
    ∑ b ∈ Finset.range n,
      growingQuotientColdRow 3
        (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
        (fun w i => preE7Y1MenuNormalizer (w := w) i)
        (fun _ _ => (153 / 200 : ℝ)) n b * ordinarySubgroupRatio b
  let Ecold := growingColdOnly_exponentialForwardEstimate coldError
    3
    (fun w i => preE7Y1MenuCoefficient lit (w := w) i)
    (fun w i => preE7Y1MenuNormalizer (w := w) i)
    (fun _ _ => (153 / 200 : ℝ))
    (by norm_num [preE7CharacterRho])
    (by norm_num [preE7CharacterRho]) (by omega)
    (fun _ i b => preE7Y1MenuCoefficient_nonneg lit i b)
    (fun _ i => preE7Y1MenuNormalizer_pos i)
    (fun _ i => (preE7Y1MenuCertificate lit i).cold_gap)
    (preE7Y1MenuMass lit)
    (Filter.Eventually.of_forall (fun _ => le_rfl))
  let Ehot := (preE7Y1MenuExceptionalBound lit hcoarse).toForwardEstimate
  simpa only [growingQuotientSecondaryError, coldError] using
    OrdinaryFrontierClosure.ExponentialForwardEstimate.add Ecold Ehot

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
