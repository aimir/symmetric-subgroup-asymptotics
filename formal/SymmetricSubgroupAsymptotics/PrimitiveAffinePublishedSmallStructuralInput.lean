import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallCatalogueBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimitiveConsumer
import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre

/-!
# Published structural input for the exceptional primitive-affine degrees

This file replaces three coarse consumer hypotheses by four precise published
inputs and constructs the finite package used by the primitive-affine
consumer.

* Roney--Dougal--Unger and PrimGrp supply the complete affine rows in degrees
  `8`, `16`, and `27`, together with the pinned representative descriptions.
* In degree `25`, the scalar/projective reduction for `GL(2,5)` uses the
  central scalar subgroup of order dividing four and
  `PGL(2,5) \cong S5`.  A soluble projective image has order at most `24`;
  a nonsoluble image is `A5` or `S5`, giving the stated composition budget.
* Halasi--Maróti's soluble linear base theorem gives the degree-`81` cube
  bound after the complement is identified with its faithful irreducible
  representation.
* The prime-degree affine classification leaves the three degree-five
  actions `C5`, `D10`, and the natural `C5 : C4` action.

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

/-- The order corollary of Halasi--Maróti, Theorem 1.1, in the form used
here.  A soluble irreducible finite linear group is completely reducible and
`p`-soluble, so their strong-base theorem gives the uniform cube bound.  The
paper gives the sharper square bound away from the ternary case; this finite
consumer only needs the cube bound at degree `81`.

Keeping the theorem at the representation level makes clear that the
degree-`81` assertion below is derived from published work, rather than
being a degree-specific project assumption. -/
def HalasiMarotiSolubleIrreducibleCubeBound : Prop :=
  ∀ {p : ℕ} [Fact p.Prime]
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Finite V],
    IsSolvable G →
      (rho : Representation (ZMod p) G V) →
      Representation.IsIrreducible rho → Function.Injective rho →
        Nat.card G ≤ Nat.card V ^ 3

/-- The three degree-five affine models in their actual action form.  The
cyclic and dihedral consumers only need a group isomorphism.  The marked
`C4` consumer needs the natural affine action itself, so its branch retains
the point relabelling rather than weakening it to an abstract group
isomorphism. -/
inductive PublishedDegreeFiveAffineModel
    (U : PreE7NonPairActionClass 5) : Type
  | cyclic
      (equiv : preE7NonPairAction 5 U ≃* Multiplicative (ZMod 5))
  | dihedral
      (equiv : preE7NonPairAction 5 U ≃* DihedralGroup 5)
  | frobenius
      (natural : ∃ e : AffineModel.V 5 1 ≃ Fin 5,
        preE7NonPairAction 5 U =
          relabelSubgroup e (AffineModel.action F20.R).range)

/-- The prime-degree affine classification specialized to degree five.
Equivalently, the point stabilizer is one of the three subgroups of
`GL(1,5) ≅ C4`, giving `C5`, `D10`, or the natural Frobenius group
`C5 : C4`. -/
def PublishedDegreeFiveAffineClassification : Prop :=
  ∀ (U : PreE7NonPairActionClass 5)
    (_P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5))
    (_hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 5 U) (Fin 5)),
      Nonempty (PublishedDegreeFiveAffineModel U)

/-- The four published finite inputs, before any consumer-specific
repackaging.  These are precisely the external facts used by the finite
primitive-affine branch: the pinned small catalogue, the standard
`GL(2,5)/PGL(2,5)` facts, Halasi--Maróti's soluble linear order theorem, and
the prime-degree affine classification at five. -/
structure PublishedPrimitiveAffineFiniteLiterature where
  smallCatalogue : PublishedPrimitiveAffineSmallCatalogueData
  degreeTwentyFive : PublishedDegreeTwentyFiveLinearData
  halasiMaroti : HalasiMarotiSolubleIrreducibleCubeBound
  degreeFive : PublishedDegreeFiveAffineClassification

namespace HalasiMarotiSolubleIrreducibleCubeBound

/-- Halasi--Maróti supplies the degree-`81` complement ceiling required by
the exceptional odd-affine consumer.  Primitivity supplies irreducibility,
and faithfulness of the original affine action supplies faithfulness of the
literal complement representation; both reductions are proved in Lean. -/
theorem degreeEightyOne
    (hHM : HalasiMarotiSolubleIrreducibleCubeBound)
    (U : PreE7NonPairActionClass 81)
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 81 U) (Fin 81))
    (x : Fin 81) (hsolvable : IsSolvable (P.complement x)) :
    Nat.card (P.complement x) ≤ 81 ^ 3 := by
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Nontrivial C.V := C.nontrivial
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  let rho := (P.complementRepresentation hprimitive C x).ρ
  have hbound : Nat.card (P.complement x) ≤ Nat.card C.V ^ 3 :=
    hHM hsolvable rho
      (P.complementRepresentation_irreducible hprimitive C x)
      (P.complementRepresentation_injective hprimitive C x)
  have hcard : Nat.card C.V = 81 := by
    calc
      Nat.card C.V = Nat.card (Multiplicative C.V) := rfl
      _ = Nat.card P.V := (Nat.card_congr C.equiv.toEquiv).symm
      _ = 81 := by simpa using P.card_eq x
  simpa [hcard] using hbound

end HalasiMarotiSolubleIrreducibleCubeBound

namespace PublishedDegreeFiveAffineModel

/-- Turn the three published degree-five action models into the exact source
sum expected by the numerical consumer.  This step only applies the three
source constructors; it assumes no counting estimate. -/
noncomputable def toSource
    {U : PreE7NonPairActionClass 5}
    (M : PublishedDegreeFiveAffineModel U) :
    PreE7SaprimDegreeFiveSource 5 U ⊕ PLift (PreE7F20Source 5 U) :=
  match M with
  | .cyclic e => Sum.inl (.c5 { equiv := e, degree := rfl })
  | .dihedral e => Sum.inl (.d10 { equiv := e, degree := rfl })
  | .frobenius natural => Sum.inr ⟨{ natural := natural }⟩

end PublishedDegreeFiveAffineModel

/-- The published degree-five classification, expressed in the legacy
source-sum interface. -/
noncomputable def degreeFiveSource_of_publishedClassification
    (h5 : PublishedDegreeFiveAffineClassification) :
    ∀ (U : PreE7NonPairActionClass 5)
      (P : PrimitiveAffineProfile (preE7NonPairAction 5 U) (Fin 5))
      (hprimitive : MulAction.IsPreprimitive
        (preE7NonPairAction 5 U) (Fin 5)),
      PreE7SaprimDegreeFiveSource 5 U ⊕ PLift (PreE7F20Source 5 U) :=
  fun U P hprimitive =>
    (Classical.choice (h5 U P hprimitive)).toSource

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

/-- **Published finite primitive-affine input.**  This is the requested
inhabitant of `PublishedPrimitiveAffineFiniteInput`.  Every consumer field is
derived from the four cited finite inputs; no epimorphism estimate, moment
bound, or asymptotic statement is included in the literature boundary. -/
noncomputable def PublishedPrimitiveAffineFiniteLiterature.toFiniteInput
    (published : PublishedPrimitiveAffineFiniteLiterature) :
    PublishedPrimitiveAffineFiniteInput :=
  publishedPrimitiveAffineFiniteInput_of_structural
    published.smallCatalogue
    published.degreeTwentyFive
    (HalasiMarotiSolubleIrreducibleCubeBound.degreeEightyOne
      published.halasiMaroti)
    (degreeFiveSource_of_publishedClassification published.degreeFive)

/-- Canonical spelling used by the global primitive-affine assembly. -/
noncomputable def publishedPrimitiveAffineFiniteInput
    (published : PublishedPrimitiveAffineFiniteLiterature) :
    PublishedPrimitiveAffineFiniteInput :=
  published.toFiniteInput

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
