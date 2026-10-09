import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopImporter
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoEightPairFiniteCatalogue

/-!
# Count-twelve and count-sixteen pair-top catalogue shapes

This file records the exact finite domains of `pair_top_actions.json`.
Count twelve has 301 degree-twelve tops, partitioned as 283 joint, eight
binary-core, eight ternary-comparator, and two paired-six rows.  The paired
rows are bound to the two auxiliary degree-six outer actions.

Count sixteen has 24 paired-eight outer actions and 29/15/20 literal
degree-sixteen actions in the zero-ternary, two-affine-block, and primitive
families.  Natural `A_16` and `S_16` are kept as theorem cases rather than
pretending that they occur in the finite files.

The resolution records below accept either the explicit pair-relative lift
conclusion or an independently constructed comparator source.  Their source
functions prove that there is no further assembly gap after those semantic
row obligations.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-! ## Exact profile menus -/

def degreeTwoPairRelativeProfile
    (binaryPrimary linear ordinary relative : ℕ) :
    DegreeTwoPairRelativeProfile where
  binaryPrimary := binaryPrimary
  linear := linear
  ordinary := ordinary
  relative := relative

/-- The five profiles occurring in the non-comparator width-24 proof:
one linear or one binary-primary prefix with relative tail four, and the
three paired-six profiles. -/
def degreeTwoTwelvePairExceptionalProfiles :
    Finset DegreeTwoPairRelativeProfile :=
  { degreeTwoPairRelativeProfile 0 1 0 4,
    degreeTwoPairRelativeProfile 1 0 0 4,
    degreeTwoPairRelativeProfile 0 0 1 3,
    degreeTwoPairRelativeProfile 2 0 0 3,
    degreeTwoPairRelativeProfile 0 0 0 4 }

/-- The generic width-24 row has its literal `kappa` ordinary prefix and
its certified homogeneous-section cap as relative tail. -/
def degreeTwoTwelvePairJointProfiles (kappa sectionCap : ℕ) :
    Finset DegreeTwoPairRelativeProfile :=
  {degreeTwoPairRelativeProfile 0 0 kappa sectionCap}

/-- The six exact width-32 profiles retained in the paper. -/
def degreeTwoSixteenPairProfiles : Finset DegreeTwoPairRelativeProfile :=
  { degreeTwoPairRelativeProfile 0 0 2 4,
    degreeTwoPairRelativeProfile 0 0 0 6,
    degreeTwoPairRelativeProfile 3 0 0 4,
    degreeTwoPairRelativeProfile 4 0 0 2,
    degreeTwoPairRelativeProfile 0 0 1 0,
    degreeTwoPairRelativeProfile 0 2 0 0 }

/-- Uniform padded numerical geometry for every count-twelve lift. -/
noncomputable def degreeTwoTwelvePairRelativeNumerics
    {p : PreE7PairActionClass 12}
    (D : DegreeTwoPairRelativeLiftData 12 p) : D.Numerics :=
  D.paddedTwoPointNumerics
    (by norm_num [preE7CharacterRho, evenWidth, halfDegree])
    (by norm_num)

/-- Uniform padded numerical geometry for every count-sixteen lift. -/
noncomputable def degreeTwoSixteenPairRelativeNumerics
    {p : PreE7PairActionClass 16}
    (D : DegreeTwoPairRelativeLiftData 16 p) : D.Numerics :=
  D.paddedTwoPointNumerics
    (by norm_num [preE7CharacterRho, evenWidth, halfDegree])
    (by norm_num)

/-! ## Reusable resolutions -/

/-- A finite top occurring one level below the top of the original pair
frame, as in the paired-six and paired-eight branches. -/
structure DegreeTwoPairTopTowerRealization {s t : ℕ}
    (D : DegreeTwoPairTopFiniteInterface t)
    (p : PreE7PairActionClass s) : Type 1 where
  frame : BinaryPairFrame (preE7PairAction s p) (Fin s)
  secondFrame : BinaryPairFrame frame.top.range (Fin t)
  topEquiv : D.top ≃* secondFrame.top.range
  module_action_eq : ∀ g v,
    permutationFunctionRepresentation (ZMod 2) D.top (Fin t) g v =
      secondFrame.coordinateTopAction (topEquiv g) v

/-- One finite top row resolved all the way to the final representative
source.  Relative rows expose the exact universal-lift conclusion and its
numerical geometry; comparator rows retain a separately constructed source. -/
inductive DegreeTwoPairTopResolvedRow {t s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface t)
    (expectedProfiles : Finset DegreeTwoPairRelativeProfile)
    (p : PreE7PairActionClass s) : Type 1 where
  | relative
      (lift : DegreeTwoPairTopRelativeLiftConclusion D p)
      (profiles_eq : lift.allowedProfiles = expectedProfiles)
      (numerics : lift.lift.Numerics)
  | comparator
      (hs : s < 24)
      (source : PreE7RankTailSourceOrYonedaTopData (2 * s)
        (preE7SmallPairNonPairAction s hs p))

namespace DegreeTwoPairTopResolvedRow

variable {t s : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
  {p : PreE7PairActionClass s}

/-- There is no remaining numerical or catalogue step after a resolved row. -/
noncomputable def source
    (hs : s < 24)
    (R : DegreeTwoPairTopResolvedRow D expectedProfiles p) :
    PreE7RankTailSourceOrYonedaTopData (2 * s)
      (preE7SmallPairNonPairAction s hs p) :=
  match R with
  | .relative lift _ numerics => lift.lift.rankTailSource hs numerics
  | .comparator _ source => source

end DegreeTwoPairTopResolvedRow

/-! ## Twelve pairs -/

inductive DegreeTwoTwelvePairTopBranch
  | joint
  | core
  | ternary
  | paired
  deriving DecidableEq

structure DegreeTwoTwelvePairTopRow : Type 1 where
  finite : DegreeTwoPairTopFiniteInterface 12
  branch : DegreeTwoTwelvePairTopBranch
  kappa : ℕ
  sectionCap : ℕ
  expectedProfiles : Finset DegreeTwoPairRelativeProfile
  expectedProfiles_eq : expectedProfiles =
    match branch with
    | .joint => degreeTwoTwelvePairJointProfiles kappa sectionCap
    | .core => degreeTwoTwelvePairExceptionalProfiles
    | .ternary => ∅
    | .paired => degreeTwoTwelvePairExceptionalProfiles

/-- Exact shape of the width-24 finite inputs.  `pairedSixBinding` prevents
the two auxiliary six-point outer actions from floating free of the two
paired degree-twelve rows. -/
structure DegreeTwoTwelvePairTopFiniteCatalogue : Type 1 where
  row : Fin 301 → DegreeTwoTwelvePairTopRow
  pairedSix : Fin 2 → DegreeTwoPairTopFiniteInterface 6
  pairedSixBinding :
    {j : Fin 301 // (row j).branch = .paired} ≃ Fin 2
  joint_count :
    (Finset.univ.filter (fun j => (row j).branch = .joint)).card = 283
  core_count :
    (Finset.univ.filter (fun j => (row j).branch = .core)).card = 8
  ternary_count :
    (Finset.univ.filter (fun j => (row j).branch = .ternary)).card = 8
  paired_count :
    (Finset.univ.filter (fun j => (row j).branch = .paired)).card = 2

/-- Published transitive degree-twelve classification, separated from all
finite normal/module checks. -/
def PublishedDegreeTwoTwelvePairTopCatalogueLocator
    (T : DegreeTwoTwelvePairTopFiniteCatalogue) : Prop :=
  ∀ p : PreE7PairActionClass 12, ∃ j : Fin 301,
    Nonempty (DegreeTwoPairTopRealization (T.row j).finite p)

/-- The row resolver is the precise remaining semantic work.  In the paired
branch it may use `pairedSixBinding` and the auxiliary degree-six interface;
in the ternary branch it may return the established interval comparator. -/
abbrev DegreeTwoTwelvePairTopCatalogueResolution
    (T : DegreeTwoTwelvePairTopFiniteCatalogue) :=
  ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
    DegreeTwoPairTopRealization (T.row j).finite p →
      DegreeTwoPairTopResolvedRow (T.row j).finite
        (T.row j).expectedProfiles p

/-- A classified and semantically resolved 301-row table supplies the exact
representative endpoint needed by the residual assembly. -/
noncomputable def degreeTwoTwelvePairRepresentativeSource_of_catalogue
    (T : DegreeTwoTwelvePairTopFiniteCatalogue)
    (published : PublishedDegreeTwoTwelvePairTopCatalogueLocator T)
    (resolve : DegreeTwoTwelvePairTopCatalogueResolution T) :
    DegreeTwoTwelvePairRepresentativeSource := by
  intro p
  obtain ⟨j, ⟨realization⟩⟩ := published p
  exact (resolve j p realization).source (by norm_num)

/-- The same table supplies the block-facing count-twelve endpoint. -/
noncomputable def degreeTwoTwelvePairResidualSource_of_catalogue
    (T : DegreeTwoTwelvePairTopFiniteCatalogue)
    (published : PublishedDegreeTwoTwelvePairTopCatalogueLocator T)
    (resolve : DegreeTwoTwelvePairTopCatalogueResolution T) :
    DegreeTwoTwelvePairResidualSource :=
  degreeTwoTwelvePairResidualSource_of_representative
    (degreeTwoTwelvePairRepresentativeSource_of_catalogue T published resolve)

/-! ## Sixteen pairs -/

/-- The four computed width-32 branches.  Their top degrees remain explicit:
the paired branch stores an outer action of degree eight, while the other
three store literal degree-sixteen tops. -/
structure DegreeTwoSixteenPairTopFiniteCatalogue : Type 1 where
  paired8 : Fin 24 → DegreeTwoPairTopFiniteInterface 8
  zero16 : Fin 29 → DegreeTwoPairTopFiniteInterface 16
  twoAffine16 : Fin 15 → DegreeTwoPairTopFiniteInterface 16
  primitive16 : Fin 20 → DegreeTwoPairTopFiniteInterface 16

inductive DegreeTwoSixteenNaturalTop
  | alternating
  | symmetric
  deriving DecidableEq

/-- Exact realization of one of the two natural primitive tops omitted from
the finite module tables because its invariant-module theorem is uniform. -/
structure DegreeTwoSixteenNaturalTopRealization
    (kind : DegreeTwoSixteenNaturalTop)
    (p : PreE7PairActionClass 16) : Type 1 where
  frame : BinaryPairFrame (preE7PairAction 16 p) (Fin 16)
  top_eq : frame.top.range =
    match kind with
    | .alternating => alternatingGroup (Fin 16)
    | .symmetric => ⊤

/-- Classification result for one actual sixteen-pair top. -/
inductive DegreeTwoSixteenPairTopLocation
    (T : DegreeTwoSixteenPairTopFiniteCatalogue)
    (p : PreE7PairActionClass 16) : Type 1 where
  | paired8 (j : Fin 24)
      (realization : DegreeTwoPairTopTowerRealization (T.paired8 j) p)
  | zero16 (j : Fin 29)
      (realization : DegreeTwoPairTopRealization (T.zero16 j) p)
  | twoAffine16 (j : Fin 15)
      (realization : DegreeTwoPairTopRealization (T.twoAffine16 j) p)
  | primitive16 (j : Fin 20)
      (realization : DegreeTwoPairTopRealization (T.primitive16 j) p)
  | natural (kind : DegreeTwoSixteenNaturalTop)
      (realization : DegreeTwoSixteenNaturalTopRealization kind p)

/-- Published primitive/block classification for the actual degree-sixteen
top, kept distinct from the four finite datasets. -/
def PublishedDegreeTwoSixteenPairTopCatalogueLocator
    (T : DegreeTwoSixteenPairTopFiniteCatalogue) : Prop :=
  ∀ p : PreE7PairActionClass 16,
    Nonempty (DegreeTwoSixteenPairTopLocation T p)

/-- Semantic resolutions for each of the four finite branches and the two
uniform natural-top theorems. -/
structure DegreeTwoSixteenPairTopCatalogueResolution
    (T : DegreeTwoSixteenPairTopFiniteCatalogue) : Type 1 where
  paired8 : ∀ (j : Fin 24) (p : PreE7PairActionClass 16),
    DegreeTwoPairTopTowerRealization (T.paired8 j) p →
      DegreeTwoPairTopResolvedRow (T.paired8 j)
        degreeTwoSixteenPairProfiles p
  zero16 : ∀ (j : Fin 29) (p : PreE7PairActionClass 16),
    DegreeTwoPairTopRealization (T.zero16 j) p →
      DegreeTwoPairTopResolvedRow (T.zero16 j)
        degreeTwoSixteenPairProfiles p
  twoAffine16 : ∀ (j : Fin 15) (p : PreE7PairActionClass 16),
    DegreeTwoPairTopRealization (T.twoAffine16 j) p →
      DegreeTwoPairTopResolvedRow (T.twoAffine16 j)
        degreeTwoSixteenPairProfiles p
  primitive16 : ∀ (j : Fin 20) (p : PreE7PairActionClass 16),
    DegreeTwoPairTopRealization (T.primitive16 j) p →
      DegreeTwoPairTopResolvedRow (T.primitive16 j)
        degreeTwoSixteenPairProfiles p
  natural : ∀ (kind : DegreeTwoSixteenNaturalTop)
      (p : PreE7PairActionClass 16),
    DegreeTwoSixteenNaturalTopRealization kind p →
      PreE7RankTailSourceOrYonedaTopData 32
        (preE7SmallPairNonPairAction 16 (by norm_num) p)

/-- A classified and resolved count-sixteen table supplies the exact
representative endpoint. -/
noncomputable def degreeTwoSixteenPairRepresentativeSource_of_catalogue
    (T : DegreeTwoSixteenPairTopFiniteCatalogue)
    (published : PublishedDegreeTwoSixteenPairTopCatalogueLocator T)
    (resolve : DegreeTwoSixteenPairTopCatalogueResolution T) :
    DegreeTwoSixteenPairRepresentativeSource := by
  intro p
  obtain ⟨location⟩ := published p
  cases location with
  | paired8 j realization =>
      exact (resolve.paired8 j p realization).source (by norm_num)
  | zero16 j realization =>
      exact (resolve.zero16 j p realization).source (by norm_num)
  | twoAffine16 j realization =>
      exact (resolve.twoAffine16 j p realization).source (by norm_num)
  | primitive16 j realization =>
      exact (resolve.primitive16 j p realization).source (by norm_num)
  | natural kind realization =>
      exact resolve.natural kind p realization

/-- The same table supplies the block-facing count-sixteen endpoint. -/
noncomputable def degreeTwoSixteenPairResidualSource_of_catalogue
    (T : DegreeTwoSixteenPairTopFiniteCatalogue)
    (published : PublishedDegreeTwoSixteenPairTopCatalogueLocator T)
    (resolve : DegreeTwoSixteenPairTopCatalogueResolution T) :
    DegreeTwoSixteenPairResidualSource :=
  degreeTwoSixteenPairResidualSource_of_representative
    (degreeTwoSixteenPairRepresentativeSource_of_catalogue
      T published resolve)

/-! ## Final degree-two assembly -/

/-- Assemble the complete degree-two residual source from the three finite
catalogues.  The remaining hypotheses are exactly the published catalogue
locators and the semantic row resolutions displayed above; there is no
project-owned count-12 or count-16 endpoint argument. -/
noncomputable def degreeTwoResidualSource_of_finitePairTopCatalogues
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedFour : PublishedDegreeTwoFourPairClassification)
    (sixPairTable : PrimitiveAffineDegreeTwoSixPairOwnerTable)
    (publishedSix : PublishedDegreeTwoSixPairCatalogueLocator sixPairTable)
    (eight : DegreeTwoEightPairFiniteCatalogue)
    (publishedEight : PublishedDegreeTwoEightPairCatalogueLocator eight)
    (twelve : DegreeTwoTwelvePairTopFiniteCatalogue)
    (publishedTwelve : PublishedDegreeTwoTwelvePairTopCatalogueLocator twelve)
    (resolveTwelve : DegreeTwoTwelvePairTopCatalogueResolution twelve)
    (sixteen : DegreeTwoSixteenPairTopFiniteCatalogue)
    (publishedSixteen :
      PublishedDegreeTwoSixteenPairTopCatalogueLocator sixteen)
    (resolveSixteen : DegreeTwoSixteenPairTopCatalogueResolution sixteen) :
    PrimitiveAffineResidualDegreeSource 2 :=
  degreeTwoResidualSource_of_eightPairCatalogue hZmud lit
    publishedThree publishedFour sixPairTable publishedSix
    eight publishedEight
    (degreeTwoTwelvePairResidualSource_of_catalogue
      twelve publishedTwelve resolveTwelve)
    (degreeTwoSixteenPairResidualSource_of_catalogue
      sixteen publishedSixteen resolveSixteen)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
