import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelOrbitAnchor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopBinaryKernelRows

/-!
# Orbit-character rows for the degree-two pair catalogues

This is the catalogue-facing form of the relative-kernel orbit theorem.  A
row supplies literal prefix characters, their common binary kernel, and
central characters whose ambient conjugacy orbits separate that kernel.
The irreducible kernel representations, their irreducible overgroup lifts,
and the final relative-kernel anchor are constructed uniformly here.

Thus finite row producers no longer have to postulate relative irreducible
representations or a faithful full tuple.  Their remaining obligation is the
finite orbit-separation statement on the displayed binary kernel.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Literal prefix and central-orbit data on one quotient. -/
structure DegreeTwoPairRelativeKernelOrbitInput
    (Q : Type) [Group Q] [Finite Q]
    (profile : DegreeTwoPairRelativeProfile) : Type 1 where
  PrefixTarget : Type
  prefixTargetGroup : Group PrefixTarget
  prefixTargetFinite : Finite PrefixTarget
  quotient : Q →* PrefixTarget
  binary : Fin profile.binaryPrimary → Q →* ℂˣ
  binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range
  linear : Fin profile.linear → Q →* ℂˣ
  ordinary : Fin profile.ordinary → FiniteIrreducibleRepresentation ℂ Q
  kernel_eq : quotient.ker =
    ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
      (⨅ i, (ordinary i).action.ker)
  kernel_twoGroup : IsPGroup 2 quotient.ker
  orbitCharacters :
    BinaryKernelOmegaOrbitCharacters quotient profile.relative

attribute [instance]
  DegreeTwoPairRelativeKernelOrbitInput.prefixTargetGroup
  DegreeTwoPairRelativeKernelOrbitInput.prefixTargetFinite

namespace DegreeTwoPairRelativeKernelOrbitInput

variable {Q : Type} [Group Q] [Finite Q]
  {profile : DegreeTwoPairRelativeProfile}
  (A : DegreeTwoPairRelativeKernelOrbitInput Q profile)

/-- Constructor used by finite producers: select canonical omega
coordinates and prove their ambient orbits separate. -/
noncomputable def ofCoordinateOrbits
    {B : Type} [Group B] [Finite B]
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (orbits : BinaryKernelOmegaCoordinateOrbits pi profile.relative) :
    DegreeTwoPairRelativeKernelOrbitInput Q profile where
  PrefixTarget := B
  prefixTargetGroup := inferInstance
  prefixTargetFinite := inferInstance
  quotient := pi
  binary := binary
  binary_twoGroup := binary_twoGroup
  linear := linear
  ordinary := ordinary
  kernel_eq := kernel_eq
  kernel_twoGroup := kernel_twoGroup
  orbitCharacters := orbits.toOrbitCharacters

/-- Constructor from an explicit spanning family of ambient dual omega
orbits.  This is the direct endpoint for module-generator arguments in the
paired-eight tower. -/
noncomputable def ofDualOrbitSpan
    {B : Type} [Group B] [Finite B]
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (orbits : BinaryKernelOmegaDualOrbitSpan pi profile.relative) :
    DegreeTwoPairRelativeKernelOrbitInput Q profile where
  PrefixTarget := B
  prefixTargetGroup := inferInstance
  prefixTargetFinite := inferInstance
  quotient := pi
  binary := binary
  binary_twoGroup := binary_twoGroup
  linear := linear
  ordinary := ordinary
  kernel_eq := kernel_eq
  kernel_twoGroup := kernel_twoGroup
  orbitCharacters := orbits.toOrbitCharacters

/-- Constructor from a generator theorem for the dual of the literal
central-omega conjugation representation.  This is the catalogue boundary
used by the coupled-head argument: its generated tuple is converted
uniformly into ambient orbit characters and then into relative
irreducibles. -/
noncomputable def ofDualGenerated
    {B : Type} [Group B] [Finite B]
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (hgen : RepresentationGeneratedBy
      (binaryKernelOmegaConjugationRepresentation pi).dual
        profile.relative) :
    DegreeTwoPairRelativeKernelOrbitInput Q profile :=
  ofDualOrbitSpan pi binary binary_twoGroup linear ordinary kernel_eq
    kernel_twoGroup (BinaryKernelOmegaDualOrbitSpan.ofDualGenerated hgen)

/-- Catalogue constructor from the semisimple detecting part of central
omega.  The supplied essentiality theorem ensures that characters which
separate this invariant subrepresentation also detect every nonzero
ambient orbit. -/
noncomputable def ofEssentialDualGenerated
    {B : Type} [Group B] [Finite B]
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (S : Subrepresentation
      (binaryKernelOmegaConjugationRepresentation pi))
    (essential : ∀ x : Additive (binaryCentralOmega pi.ker), x ≠ 0 →
      ∃ y : S.toSubmodule, y ≠ 0 ∧
        (y : Additive (binaryCentralOmega pi.ker)) ∈
          binaryOrbitSpan
            (binaryKernelOmegaConjugationRepresentation pi) x)
    (hgen : RepresentationGeneratedBy S.toRepresentation.dual
      profile.relative) :
    DegreeTwoPairRelativeKernelOrbitInput Q profile where
  PrefixTarget := B
  prefixTargetGroup := inferInstance
  prefixTargetFinite := inferInstance
  quotient := pi
  binary := binary
  binary_twoGroup := binary_twoGroup
  linear := linear
  ordinary := ordinary
  kernel_eq := kernel_eq
  kernel_twoGroup := kernel_twoGroup
  orbitCharacters :=
    (BinaryKernelOmegaLinearOrbits.ofEssentialDualGenerated
      S essential hgen).toOrbitCharacters

/-- Canonical semisimple-socle constructor.  Finite-module essentiality is
proved once in the generic orbit layer, so a row only supplies a generator
theorem for the dual of omega's actual representation socle. -/
noncomputable def ofSocleDualGenerated
    {B : Type} [Group B] [Finite B]
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    (hgen : RepresentationGeneratedBy
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.dual
      profile.relative) :
    DegreeTwoPairRelativeKernelOrbitInput Q profile where
  PrefixTarget := B
  prefixTargetGroup := inferInstance
  prefixTargetFinite := inferInstance
  quotient := pi
  binary := binary
  binary_twoGroup := binary_twoGroup
  linear := linear
  ordinary := ordinary
  kernel_eq := kernel_eq
  kernel_twoGroup := kernel_twoGroup
  orbitCharacters :=
    (BinaryKernelOmegaLinearOrbits.ofSocleDualGenerated hgen).toOrbitCharacters

/-- Catalogue endpoint for a Schur-capacity proof on the dual of the
canonical omega socle. -/
noncomputable def ofSocleDualSchurCapacity
    {B : Type} [Group B] [Finite B]
    (pi : Q →* B)
    (binary : Fin profile.binaryPrimary → Q →* ℂˣ)
    (binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range)
    (linear : Fin profile.linear → Q →* ℂˣ)
    (ordinary : Fin profile.ordinary →
      FiniteIrreducibleRepresentation ℂ Q)
    (kernel_eq : pi.ker =
      ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
        (⨅ i, (ordinary i).action.ker))
    (kernel_twoGroup : IsPGroup 2 pi.ker)
    [IsSemisimpleModule (ZMod 2)[Q]
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.dual.asModule]
    (hcap : representationSchurCapacity
      (finiteRepresentationSocle
        (binaryKernelOmegaConjugationRepresentation pi)).toRepresentation.dual ≤
      profile.relative) :
    DegreeTwoPairRelativeKernelOrbitInput Q profile where
  PrefixTarget := B
  prefixTargetGroup := inferInstance
  prefixTargetFinite := inferInstance
  quotient := pi
  binary := binary
  binary_twoGroup := binary_twoGroup
  linear := linear
  ordinary := ordinary
  kernel_eq := kernel_eq
  kernel_twoGroup := kernel_twoGroup
  orbitCharacters :=
    (BinaryKernelOmegaLinearOrbits.ofSocleDualSchurCapacity
      hcap).toOrbitCharacters

/-- Construct the full relative-kernel anchor from the literal finite
orbit-character input. -/
noncomputable def anchor : DegreeTwoPairRelativeKernelAnchor Q profile :=
  DegreeTwoPairRelativeKernelAnchor.ofBinaryKernelOmegaOrbitCharacters
    A.quotient A.binary A.binary_twoGroup A.linear A.ordinary
    A.kernel_eq A.kernel_twoGroup
    A.orbitCharacters

end DegreeTwoPairRelativeKernelOrbitInput

/-! ## One-frame rows -/

/-- One-frame catalogue row whose relative tail is supplied by literal
central-orbit characters on each original quotient. -/
structure DegreeTwoPairTopRelativeKernelOrbitRowData {s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface s)
    (expectedProfiles : Finset DegreeTwoPairRelativeProfile)
    (p : PreE7PairActionClass s)
    (realization : DegreeTwoPairTopRealization D p) : Type 1 where
  stateProfile : DegreeTwoPairTopStateProfile D p realization
  profiles_eq : stateProfile.allowedProfiles = expectedProfiles
  input : ∀ N, DegreeTwoPairRelativeKernelOrbitInput
    (preE7PairAction s p ⨸ N.1) (stateProfile.profile N)

namespace DegreeTwoPairTopRelativeKernelOrbitRowData

variable {s : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
  {p : PreE7PairActionClass s}
  {realization : DegreeTwoPairTopRealization D p}
  (A : DegreeTwoPairTopRelativeKernelOrbitRowData
    D expectedProfiles p realization)

/-- The orbit-character input resolves every original normal in the row. -/
noncomputable def liftConclusion (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeLiftConclusion D p :=
  A.stateProfile.relativeKernelLiftConclusion lit
    (fun N ↦ (A.input N).anchor)

theorem liftConclusion_profiles_eq (lit : PreE7CharacterLiterature) :
    (A.liftConclusion lit).allowedProfiles = expectedProfiles := by
  change A.stateProfile.allowedProfiles = expectedProfiles
  exact A.profiles_eq

noncomputable def twelveResolvedData
    {D : DegreeTwoPairTopFiniteInterface 12}
    {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
    {p : PreE7PairActionClass 12}
    {realization : DegreeTwoPairTopRealization D p}
    (A : DegreeTwoPairTopRelativeKernelOrbitRowData
      D expectedProfiles p realization)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeResolvedData D expectedProfiles p := by
  let lift := A.liftConclusion lit
  exact
    { lift := lift
      profiles_eq := A.liftConclusion_profiles_eq lit
      numerics := degreeTwoTwelvePairRelativeNumerics lift.lift }

noncomputable def sixteenResolvedData
    {D : DegreeTwoPairTopFiniteInterface 16}
    {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
    {p : PreE7PairActionClass 16}
    {realization : DegreeTwoPairTopRealization D p}
    (A : DegreeTwoPairTopRelativeKernelOrbitRowData
      D expectedProfiles p realization)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeResolvedData D expectedProfiles p := by
  let lift := A.liftConclusion lit
  exact
    { lift := lift
      profiles_eq := A.liftConclusion_profiles_eq lit
      numerics := degreeTwoSixteenPairRelativeNumerics lift.lift }

end DegreeTwoPairTopRelativeKernelOrbitRowData

/-! ## Two-frame rows -/

/-- Paired-eight catalogue row with the same orbit-character payload after
the second pair frame selects the finite top and module states. -/
structure DegreeTwoPairTopTowerRelativeKernelOrbitRowData {s t : ℕ}
    (D : DegreeTwoPairTopFiniteInterface t)
    (expectedProfiles : Finset DegreeTwoPairRelativeProfile)
    (p : PreE7PairActionClass s)
    (realization : DegreeTwoPairTopTowerRealization D p) : Type 1 where
  stateProfile : DegreeTwoPairTopTowerStateProfile D p realization
  profiles_eq : stateProfile.allowedProfiles = expectedProfiles
  input : ∀ N, DegreeTwoPairRelativeKernelOrbitInput
    (preE7PairAction s p ⨸ N.1) (stateProfile.profile N)

namespace DegreeTwoPairTopTowerRelativeKernelOrbitRowData

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
  {p : PreE7PairActionClass s}
  {realization : DegreeTwoPairTopTowerRealization D p}
  (A : DegreeTwoPairTopTowerRelativeKernelOrbitRowData
    D expectedProfiles p realization)

noncomputable def liftConclusion (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeLiftConclusion D p :=
  A.stateProfile.relativeKernelLiftConclusion lit
    (fun N ↦ (A.input N).anchor)

theorem liftConclusion_profiles_eq (lit : PreE7CharacterLiterature) :
    (A.liftConclusion lit).allowedProfiles = expectedProfiles := by
  change A.stateProfile.allowedProfiles = expectedProfiles
  exact A.profiles_eq

noncomputable def sixteenResolvedData
    {D : DegreeTwoPairTopFiniteInterface 8}
    {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
    {p : PreE7PairActionClass 16}
    {realization : DegreeTwoPairTopTowerRealization D p}
    (A : DegreeTwoPairTopTowerRelativeKernelOrbitRowData
      D expectedProfiles p realization)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeResolvedData D expectedProfiles p := by
  let lift := A.liftConclusion lit
  exact
    { lift := lift
      profiles_eq := A.liftConclusion_profiles_eq lit
      numerics := degreeTwoSixteenPairRelativeNumerics lift.lift }

end DegreeTwoPairTopTowerRelativeKernelOrbitRowData

/-! ## Catalogue resolvers -/

/-- Resolve count twelve directly from orbit-character rows and the eight
concrete ternary comparators. -/
noncomputable def degreeTwoTwelveResolution_of_relativeKernelOrbits_and_ternary
    (lit : PreE7CharacterLiterature)
    (T : DegreeTwoTwelvePairTopFiniteCatalogue)
    (relative : ∀ (j : Fin 301) (p : PreE7PairActionClass 12)
      (realization : DegreeTwoPairTopRealization (T.row j).finite p),
      (T.row j).branch ≠ .ternary →
      DegreeTwoPairTopRelativeKernelOrbitRowData
        (T.row j).finite (T.row j).expectedProfiles p realization)
    (ternary : ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
      DegreeTwoPairTopRealization (T.row j).finite p →
      (T.row j).branch = .ternary →
      DegreeTwoTwelveTernaryComparatorData p) :
    DegreeTwoTwelvePairTopCatalogueResolution T :=
  degreeTwoTwelveResolution_of_relative_and_ternary T
    (fun j p realization h ↦
      (relative j p realization h).twelveResolvedData lit)
    ternary

/-- Resolve count sixteen directly from one- and two-frame orbit-character
rows, retaining the structural natural-top theorem. -/
noncomputable def degreeTwoSixteenResolution_of_relativeKernelOrbits_and_naturalSocle
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (T : DegreeTwoSixteenPairTopFiniteCatalogue)
    (paired8 : ∀ (j : Fin 24) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopTowerRealization (T.paired8 j) p),
      DegreeTwoPairTopTowerRelativeKernelOrbitRowData
        (T.paired8 j) degreeTwoSixteenPairProfiles p realization)
    (zero16 : ∀ (j : Fin 29) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization (T.zero16 j) p),
      DegreeTwoPairTopRelativeKernelOrbitRowData
        (T.zero16 j) degreeTwoSixteenPairProfiles p realization)
    (twoAffine16 : ∀ (j : Fin 15) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization (T.twoAffine16 j) p),
      DegreeTwoPairTopRelativeKernelOrbitRowData
        (T.twoAffine16 j) degreeTwoSixteenPairProfiles p realization)
    (primitive16 : ∀ (j : Fin 20) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization (T.primitive16 j) p),
      DegreeTwoPairTopRelativeKernelOrbitRowData
        (T.primitive16 j) degreeTwoSixteenPairProfiles p realization)
    (natural : ∀ (kind : DegreeTwoSixteenNaturalTop)
      (p : PreE7PairActionClass 16)
      (realization : DegreeTwoSixteenNaturalTopRealization kind p),
      DegreeTwoSixteenNaturalSocleGeneratorData kind p realization) :
    DegreeTwoSixteenPairTopCatalogueResolution T where
  paired8 j p realization :=
    ((paired8 j p realization).sixteenResolvedData lit).toResolvedRow
  zero16 j p realization :=
    ((zero16 j p realization).sixteenResolvedData lit).toResolvedRow
  twoAffine16 j p realization :=
    ((twoAffine16 j p realization).sixteenResolvedData lit).toResolvedRow
  primitive16 j p realization :=
    ((primitive16 j p realization).sixteenResolvedData lit).toResolvedRow
  natural kind p realization :=
    (natural kind p realization).source hZmud lit

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
