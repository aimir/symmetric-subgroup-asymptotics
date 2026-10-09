import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopCatalogues
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopOriginalNormalSignature

/-!
# Concrete comparator and natural branches of the pair-top catalogues

The generic catalogue shape permits a row resolver to return an arbitrary
already-built source.  This file removes that freedom in the two branches
which do not use the relative finite table.

* A count-twelve ternary row is installed from the ordinary finite QCHAR
  importer, with its literal quotient action checked to have degree eight.
* A natural `A_16` or `S_16` top is installed from the stated one-general or
  two-linear quotient-character alternative, using the ordinary character
  envelope and the same automatic pair numerical package.

The assembly functions at the end accept relative-lift conclusions on every
remaining finite row and return the existing catalogue resolution types.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Data retained after a finite row has been resolved by the universal
relative-lift theorem. -/
structure DegreeTwoPairTopRelativeResolvedData {t s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface t)
    (expectedProfiles : Finset DegreeTwoPairRelativeProfile)
    (p : PreE7PairActionClass s) : Type 1 where
  lift : DegreeTwoPairTopRelativeLiftConclusion D p
  profiles_eq : lift.allowedProfiles = expectedProfiles
  numerics : lift.lift.Numerics

namespace DegreeTwoPairTopRelativeResolvedData

variable {t s : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
  {p : PreE7PairActionClass s}

noncomputable def toResolvedRow
    (R : DegreeTwoPairTopRelativeResolvedData D expectedProfiles p) :
    DegreeTwoPairTopResolvedRow D expectedProfiles p :=
  .relative R.lift R.profiles_eq R.numerics

end DegreeTwoPairTopRelativeResolvedData

/-! ## Count-twelve ternary comparator rows -/

/-- The exact imported payload of a ternary comparator row.  The interval
comparator is a faithful action of the literal quotient on eight points;
all remaining normal axes are the finite QCHAR character rows. -/
structure DegreeTwoTwelveTernaryComparatorData
    (p : PreE7PairActionClass 12) : Type 1 where
  qchar : PreE7FiniteQcharMenuData 24
    (preE7SmallPairNonPairAction 12 (by norm_num) p)
  comparator_degree : qchar.axes.degree = 8

namespace DegreeTwoTwelveTernaryComparatorData

variable {p : PreE7PairActionClass 12}

/-- A checked ternary QCHAR payload is already the concrete final source. -/
noncomputable def source (C : DegreeTwoTwelveTernaryComparatorData p) :
    PreE7RankTailSourceOrYonedaTopData 24
      (preE7SmallPairNonPairAction 12 (by norm_num) p) :=
  C.qchar.rankTailSource

/-- Install the concrete degree-eight quotient comparator in a ternary
catalogue row. -/
noncomputable def resolvedRow
    {D : DegreeTwoPairTopFiniteInterface 12}
    {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
    (C : DegreeTwoTwelveTernaryComparatorData p) :
    DegreeTwoPairTopResolvedRow D expectedProfiles p :=
  .comparator (by norm_num) C.source

end DegreeTwoTwelveTernaryComparatorData

/-- Assemble the full count-twelve resolver while forcing exactly the eight
ternary rows through the finite QCHAR importer.  Every other row must supply
the relative-lift conclusion and its automatically checked numerics. -/
noncomputable def degreeTwoTwelveResolution_of_relative_and_ternary
    (T : DegreeTwoTwelvePairTopFiniteCatalogue)
    (relative : ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
      DegreeTwoPairTopRealization (T.row j).finite p →
      (T.row j).branch ≠ .ternary →
      DegreeTwoPairTopRelativeResolvedData (T.row j).finite
        (T.row j).expectedProfiles p)
    (ternary : ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
      DegreeTwoPairTopRealization (T.row j).finite p →
      (T.row j).branch = .ternary →
      DegreeTwoTwelveTernaryComparatorData p) :
    DegreeTwoTwelvePairTopCatalogueResolution T := by
  intro j p realization
  by_cases h : (T.row j).branch = .ternary
  · exact (ternary j p realization h).resolvedRow
  · exact (relative j p realization h).toResolvedRow

/-! ## Natural alternating and symmetric count-sixteen tops -/

/-- The two character shapes in the natural-top theorem: one ordinary
irreducible, or two unrestricted linear characters. -/
def DegreeTwoSixteenNaturalCharacterShape
    {Q : Type} [Group Q] (c : CharacterQuotientCertificate Q) : Prop :=
  (c.tuple.binaryCount = 0 ∧ c.tuple.linearCount = 0 ∧
      c.tuple.generalCount = 1) ∨
    (c.tuple.binaryCount = 0 ∧ c.tuple.linearCount = 2 ∧
      c.tuple.generalCount = 0)

/-- Per-original-quotient character data supplied by the natural
alternating/symmetric top theorem.  The realization keeps the natural top
attached to the same original pair frame. -/
structure DegreeTwoSixteenNaturalCharacterData
    (kind : DegreeTwoSixteenNaturalTop)
    (p : PreE7PairActionClass 16)
    (realization : DegreeTwoSixteenNaturalTopRealization kind p) : Type 1 where
  certificate : ∀ N,
    CharacterQuotientCertificate (preE7PairAction 16 p ⨸ N.1)
  mixed : ∀ N, (certificate N).mode = .mixed
  shape : ∀ N, DegreeTwoSixteenNaturalCharacterShape (certificate N)
  capacity : ∀ N,
    (certificate N).slope ≤ preE7CharacterWindow 32

namespace DegreeTwoSixteenNaturalCharacterData

variable {kind : DegreeTwoSixteenNaturalTop}
  {p : PreE7PairActionClass 16}
  {realization : DegreeTwoSixteenNaturalTopRealization kind p}
  (C : DegreeTwoSixteenNaturalCharacterData kind p realization)

/-- The natural-top character alternative gives universal lift data on all
literal original normal quotients. -/
noncomputable def liftData (lit : PreE7CharacterLiterature) :
    DegreeTwoPairRelativeLiftData 16 p :=
  DegreeTwoPairRelativeLiftData.ofMixedCharacterCertificates
    lit C.certificate C.mixed C.capacity

/-- Concrete final source for the natural `A_16`/`S_16` branch. -/
noncomputable def source (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 32
      (preE7SmallPairNonPairAction 16 (by norm_num) p) :=
  let D := C.liftData lit
  D.rankTailSource (by norm_num)
    (degreeTwoSixteenPairRelativeNumerics D)

end DegreeTwoSixteenNaturalCharacterData

/-- Assemble the count-sixteen resolver with relative lifts on all four
finite branches and the explicit natural-top character theorem on the two
uniform branches. -/
noncomputable def degreeTwoSixteenResolution_of_relative_and_natural
    (lit : PreE7CharacterLiterature)
    (T : DegreeTwoSixteenPairTopFiniteCatalogue)
    (paired8 : ∀ (j : Fin 24) (p : PreE7PairActionClass 16),
      DegreeTwoPairTopTowerRealization (T.paired8 j) p →
      DegreeTwoPairTopRelativeResolvedData (T.paired8 j)
        degreeTwoSixteenPairProfiles p)
    (zero16 : ∀ (j : Fin 29) (p : PreE7PairActionClass 16),
      DegreeTwoPairTopRealization (T.zero16 j) p →
      DegreeTwoPairTopRelativeResolvedData (T.zero16 j)
        degreeTwoSixteenPairProfiles p)
    (twoAffine16 : ∀ (j : Fin 15) (p : PreE7PairActionClass 16),
      DegreeTwoPairTopRealization (T.twoAffine16 j) p →
      DegreeTwoPairTopRelativeResolvedData (T.twoAffine16 j)
        degreeTwoSixteenPairProfiles p)
    (primitive16 : ∀ (j : Fin 20) (p : PreE7PairActionClass 16),
      DegreeTwoPairTopRealization (T.primitive16 j) p →
      DegreeTwoPairTopRelativeResolvedData (T.primitive16 j)
        degreeTwoSixteenPairProfiles p)
    (natural : ∀ (kind : DegreeTwoSixteenNaturalTop)
      (p : PreE7PairActionClass 16)
      (realization : DegreeTwoSixteenNaturalTopRealization kind p),
      DegreeTwoSixteenNaturalCharacterData kind p realization) :
    DegreeTwoSixteenPairTopCatalogueResolution T where
  paired8 j p realization := (paired8 j p realization).toResolvedRow
  zero16 j p realization := (zero16 j p realization).toResolvedRow
  twoAffine16 j p realization := (twoAffine16 j p realization).toResolvedRow
  primitive16 j p realization := (primitive16 j p realization).toResolvedRow
  natural kind p realization := (natural kind p realization).source lit

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
