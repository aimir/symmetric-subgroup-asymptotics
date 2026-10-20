import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveJointFiniteRows

/-!
A literal joint action may use any proved parameter pair in the existing
width-24 numerical menu. Its historical profile is sufficient but is not
required by the counting theorem. An alternate package supplies an actual
source through the existing comparator constructor; it does not assert
that the alternate profile equals the historical one.

Every quotient-socle and natural-module bound below is still on the exact
original top. The numerical window, realization, and action weights are
unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveFlexibleProfiles

open DegreeTwoTwelveJointFiniteRows

/-- A proved package at an explicitly admissible pair of capacities. -/
structure Data (D : DegreeTwoPairTopFiniteInterface 12) : Type 1 where
  kappa : ℕ
  sectionCap : ℕ
  parameters : (kappa, sectionCap) ∈ degreeTwoTwelvePairJointParameters
  finite : DegreeTwoTwelveJointFiniteRowData D kappa sectionCap

namespace Data

variable {D : DegreeTwoPairTopFiniteInterface 12} (F : Data D)

/-- The source is proved from the alternate finite bounds and the same
checked numerical window; it is not an additional assumption. -/
noncomputable def source
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p) :
    PreE7RankTailSourceOrYonedaTopData (2 * 12)
      (preE7SmallPairNonPairAction 12 (by decide) p) := by
  let lift := F.finite.liftConclusion hZmud lit F.parameters R
  exact lift.lift.rankTailSource (by decide)
    (degreeTwoTwelvePairRelativeNumerics lift.lift)

/-- Resolve an original row without falsely identifying a new admissible
profile with its historical stored profile. -/
noncomputable def resolvedRow
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (expectedProfiles : Finset DegreeTwoPairRelativeProfile)
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopResolvedRow D expectedProfiles p :=
  .comparator (by decide) (F.source hZmud lit R)

/-- Every existing exact package remains usable without altering it. -/
noncomputable def ofExact {kappa sectionCap : ℕ}
    (F : DegreeTwoTwelveJointFiniteRowData D kappa sectionCap)
    (hparameters : (kappa, sectionCap) ∈ degreeTwoTwelvePairJointParameters) :
    Data D where
  kappa := kappa
  sectionCap := sectionCap
  parameters := hparameters
  finite := F

end Data

end DegreeTwoTwelveFlexibleProfiles
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
