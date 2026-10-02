import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimitiveConsumer

/-!
# Published structural input for the exceptional primitive-affine degrees

This file replaces three coarse consumer hypotheses by two precise published
inputs.

* Roney--Dougal--Unger and PrimGrp supply the complete affine rows in degrees
  `8`, `16`, and `27`, together with the pinned representative descriptions.
* In degree `25`, the scalar/projective reduction for `GL(2,5)` uses the
  central scalar subgroup of order dividing four and
  `PGL(2,5) \cong S5`.  A soluble projective image has order at most `24`;
  a nonsoluble image is `A5` or `S5`, giving the stated composition budget.

All normal-quotient propagation, chief-series transport, finite maxima, and
consumer assembly are proved in Lean.  The published boundary contains no
epimorphism count, moment estimate, or asymptotic inequality.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The pinned published catalogue and the exact representative facts used
from it.  The representative receipt records ordinary finite-group
properties of the groups named in the PrimGrp rows; it is not a new
classification assertion. -/
structure PublishedPrimitiveAffineSmallCatalogueData where
  locator : PublishedSmallAffineCatalogueLocator
  representativeFacts : SmallAffineCatalogueReceipt locator

/-- The standard scalar/projective facts for irreducible subgroups of
`GL(2,5)`.  The first field is deliberately only the top projective datum:
`DegreeTwentyFiveCentralFourModel.ofTopDatum` proves its propagation to every
normal quotient. -/
structure PublishedDegreeTwentyFiveLinearData where
  solubleProjective : ∀ (U : PreE7NonPairActionClass 25)
    (P : PrimitiveAffineProfile (preE7NonPairAction 25 U) (Fin 25))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 25 U) (Fin 25))
    (x : Fin 25), IsSolvable (P.complement x) →
      CentralFourQuotientDatum (P.complement x)
  nonsolubleComposition : ∀ (U : PreE7NonPairActionClass 25)
    (P : PrimitiveAffineProfile (preE7NonPairAction 25 U) (Fin 25))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 25 U) (Fin 25))
    (x : Fin 25) (T : FixedTargetCompositionTrace (P.complement x)),
    ¬ IsSolvable (P.complement x) → T.envelope.abelianLength ≤ 3

namespace PublishedPrimitiveAffineSmallCatalogueData

/-- The degree-`27` soluble complement ceiling is the checked maximum of the
nine soluble published rows. -/
theorem degreeTwentySeven_card_le
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (U : PreE7NonPairActionClass 27)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 27 U) (Fin 27))
    (P : PrimitiveAffineProfile (preE7NonPairAction 27 U) (Fin 27))
    (x : Fin 27) (hsolvable : IsSolvable (P.complement x)) :
    Nat.card (P.complement x) ≤ 78 :=
  PrimitiveAffineSmallCatalogueBridge.degreeTwentySeven_card_le
    D.locator D.representativeFacts U hprimitive P x hsolvable

/-- Assemble the former four-degree nonsoluble input from the published
catalogue at `8`, `16`, `27` and the standard degree-`25` projective fact. -/
noncomputable def nonsolubleCompositionInput
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (D25 : PublishedDegreeTwentyFiveLinearData) :
    PublishedNonsolublePrimitiveAffineSmallCompositionInput where
  degreeEight U P hprimitive x T hnonsolvable :=
    PrimitiveAffineSmallCatalogueBridge.degreeEight_abelianLength_eq_zero
      D.locator D.representativeFacts U hprimitive P x T hnonsolvable
  degreeSixteen U P hprimitive x T hnonsolvable :=
    PrimitiveAffineSmallCatalogueBridge.degreeSixteen_abelianLength_le_two
      D.locator D.representativeFacts U hprimitive P x T hnonsolvable
  degreeTwentyFive U P hprimitive x T hnonsolvable :=
    D25.nonsolubleComposition U P hprimitive x T hnonsolvable
  degreeTwentySeven U P hprimitive x T hnonsolvable :=
    PrimitiveAffineSmallCatalogueBridge.degreeTwentySeven_abelianLength_le_one
      D.locator D.representativeFacts U hprimitive P x T hnonsolvable

/-- Assemble the degree-`25` soluble central input.  The all-quotients model
is subsequently derived in Lean from this top datum. -/
noncomputable def solubleCentralInput
    (_D : PublishedPrimitiveAffineSmallCatalogueData)
    (D25 : PublishedDegreeTwentyFiveLinearData) :
    PublishedSolublePrimitiveAffineSmallCentralInput where
  degreeTwentyFiveProjectiveDatum U P hprimitive x hsolvable :=
    D25.solubleProjective U P hprimitive x hsolvable

/-- Add the separately published degree-`81` order theorem to obtain the old
two-degree odd exceptional interface. -/
noncomputable def solubleOddInput
    (D : PublishedPrimitiveAffineSmallCatalogueData)
    (degreeEightyOne : ∀ (U : PreE7NonPairActionClass 81)
      (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
      (_hprimitive : MulAction.IsPreprimitive
        (preE7NonPairAction 81 U) (Fin 81))
      (x : Fin 81), IsSolvable (P.complement x) →
        Nat.card (P.complement x) ≤ 81 ^ 3) :
    PublishedSolublePrimitiveAffineExceptionalOrderInput where
  degreeTwentySeven U P hprimitive x hsolvable :=
    D.degreeTwentySeven_card_le U hprimitive P x hsolvable
  degreeEightyOne := degreeEightyOne

end PublishedPrimitiveAffineSmallCatalogueData

/-- The exact published inputs imply the legacy finite-input package used by
the exhaustive primitive-affine consumer. -/
noncomputable def publishedPrimitiveAffineFiniteInput_of_structural
    (small : PublishedPrimitiveAffineSmallCatalogueData)
    (degree25 : PublishedDegreeTwentyFiveLinearData)
    (degreeEightyOne : ∀ (U : PreE7NonPairActionClass 81)
      (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
      (_hprimitive : MulAction.IsPreprimitive
        (preE7NonPairAction 81 U) (Fin 81))
      (x : Fin 81), IsSolvable (P.complement x) →
        Nat.card (P.complement x) ≤ 81 ^ 3)
    (degreeFive : ∀ (U : PreE7NonPairActionClass 5)
      (_P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5))
      (_hprimitive : MulAction.IsPreprimitive
        (preE7NonPairAction 5 U) (Fin 5)),
        PreE7SaprimDegreeFiveSource 5 U ⊕ PLift (PreE7F20Source 5 U)) :
    PublishedPrimitiveAffineFiniteInput where
  nonsolubleSmall := small.nonsolubleCompositionInput degree25
  solubleOdd := small.solubleOddInput degreeEightyOne
  solubleCentral := small.solubleCentralInput degree25
  degreeFive := degreeFive

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
