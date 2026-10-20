import SymmetricSubgroupAsymptotics.BinaryPairTernaryNormalizerPrefix
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10BinaryQuotientPilot

/-!
# Literal row-10 finite data for the ternary normalizer branch

The checked point chart reduces cubic fixed-point-freeness to twenty-four
model elements and twelve original points. Together with order twenty-four
this supplies the generic normalizer branch for every original binary
quotient of every row-10 realization.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10NormalizerPrefix

open PrimitiveAffineDegreeTwoTwelveRow10BinaryQuotientPilot
open BinaryPairTernaryNormalizerPrefix
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem model_cubic_fixedPointFree
    (g : Model) (hg : g ^ 3 = 1) (hne : g ≠ 1) (x : Fin 12) :
    literalAction g x ≠ x := by
  decide +kernel +revert

theorem literalTopCertificate :
    LiteralTopCertificate DegreeTwoTwelvePairFiniteCatalogue.row10Interface where
  three_dvd := by
    change 3 ∣ Nat.card Top
    rw [top_card]
    decide
  nine_not_dvd := by
    change ¬ 9 ∣ Nat.card Top
    rw [top_card]
    decide
  cubic_fixedPointFree := by
    intro t ht htne i
    obtain ⟨g, rfl⟩ := modelEquiv.surjective t
    have hg : g ^ 3 = 1 := by
      apply modelEquiv.injective
      simpa only [map_pow, map_one] using ht
    have hgne : g ≠ 1 := by
      intro h
      exact htne ((congrArg modelEquiv h).trans modelEquiv.map_one)
    change literalAction g i ≠ i
    exact model_cubic_fixedPointFree g hg hgne i

theorem binary_quotient_orbitInput
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization DegreeTwoTwelvePairFiniteCatalogue.row10Interface p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hQ : IsPGroup 2 (preE7PairAction 12 p ⧸ N.1)) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput
      (preE7PairAction 12 p ⧸ N.1) (degreeTwoPairRelativeProfile 1 0 0 4)) :=
  literal_binary_quotient_orbitInput literalTopCertificate R N hQ

theorem binary_top_quotient_orbitInput
    {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization DegreeTwoTwelvePairFiniteCatalogue.row10Interface p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hbinaryTop : IsPGroup 2
      (DegreeTwoTwelvePairFiniteCatalogue.row10Interface.top ⧸
        DegreeTwoTwelvePairFiniteCatalogue.row10Interface.normalRegistry.state
          (R.topNormalState N))) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput
      (preE7PairAction 12 p ⧸ N.1) (degreeTwoPairRelativeProfile 1 0 0 4)) :=
  literal_binary_top_quotient_orbitInput literalTopCertificate R N hbinaryTop

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10NormalizerPrefix
