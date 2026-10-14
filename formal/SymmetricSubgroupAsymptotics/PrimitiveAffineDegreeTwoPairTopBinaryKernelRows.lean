import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoBinaryKernelAnchor
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopConcreteBranches

/-!
# Binary-kernel rows for the degree-two pair catalogues

This file connects the universal binary-kernel lift to the concrete
count-twelve and count-sixteen row APIs.  A finite row now supplies actual
prefix characters on each literal quotient and identifies their common
binary kernel.  The relative label, its kernel theorem, and its cardinality
bound are then constructed uniformly by
`DegreeTwoPairBinaryKernelAnchor.toQuotientEnvelope`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- One-frame row data after replacing an abstract relative-label
certificate by the actual fixed-prefix binary kernel. -/
structure DegreeTwoPairTopBinaryKernelRowData {s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface s)
    (expectedProfiles : Finset DegreeTwoPairRelativeProfile)
    (p : PreE7PairActionClass s)
    (realization : DegreeTwoPairTopRealization D p) : Type 1 where
  stateProfile : DegreeTwoPairTopStateProfile D p realization
  profiles_eq : stateProfile.allowedProfiles = expectedProfiles
  anchor : ∀ N, DegreeTwoPairBinaryKernelAnchor
    (preE7PairAction s p ⧸ N.1) (stateProfile.profile N)

namespace DegreeTwoPairTopBinaryKernelRowData

variable {s : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
  {p : PreE7PairActionClass s}
  {realization : DegreeTwoPairTopRealization D p}
  (A : DegreeTwoPairTopBinaryKernelRowData
    D expectedProfiles p realization)

/-- The universal binary-kernel theorem resolves every original normal of
the row. -/
noncomputable def liftConclusion (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeLiftConclusion D p := by
  let lift : DegreeTwoPairRelativeLiftData s p :=
    DegreeTwoPairRelativeLiftData.ofBinaryKernelAnchors lit
      A.stateProfile.profile A.stateProfile.capacity A.anchor
  exact
    { lift := lift
      topNormalState := realization.topNormalState
      moduleState := realization.moduleState
      profileOfState := A.stateProfile.profileOfState
      profile_eq := fun _ ↦ rfl
      allowedProfiles := A.stateProfile.allowedProfiles
      allowed_capacity := A.stateProfile.allowed_capacity
      profile_mem := A.stateProfile.profile_mem }

theorem liftConclusion_profiles_eq (lit : PreE7CharacterLiterature) :
    (A.liftConclusion lit).allowedProfiles = expectedProfiles := by
  change A.stateProfile.allowedProfiles = expectedProfiles
  exact A.profiles_eq

/-- Generic constructor from a literal finite state table. -/
noncomputable def ofProfileTable
    (allowedProfiles : Finset DegreeTwoPairRelativeProfile)
    (allowed_capacity : ∀ profile ∈ allowedProfiles,
      profile.slope ≤ preE7CharacterWindow (2 * s))
    (profileOfState : D.normalRegistry.State → D.ModuleState →
      DegreeTwoPairRelativeProfile)
    (profile_mem : ∀ N,
      profileOfState (realization.topNormalState N)
        (realization.moduleState N) ∈ allowedProfiles)
    (anchor : ∀ N, DegreeTwoPairBinaryKernelAnchor
      (preE7PairAction s p ⧸ N.1)
      (profileOfState (realization.topNormalState N)
        (realization.moduleState N))) :
    DegreeTwoPairTopBinaryKernelRowData D allowedProfiles p realization :=
  { stateProfile :=
      { profileOfState := profileOfState
        allowedProfiles := allowedProfiles
        allowed_capacity := allowed_capacity
        profile_mem := profile_mem }
    profiles_eq := rfl
    anchor := anchor }

/-- Count-twelve exceptional-profile specialization. -/
noncomputable def twelveExceptionalOfProfileTable
    {D : DegreeTwoPairTopFiniteInterface 12}
    {p : PreE7PairActionClass 12}
    {realization : DegreeTwoPairTopRealization D p}
    (profileOfState : D.normalRegistry.State → D.ModuleState →
      DegreeTwoPairRelativeProfile)
    (profile_mem : ∀ N,
      profileOfState (realization.topNormalState N)
        (realization.moduleState N) ∈
          degreeTwoTwelvePairExceptionalProfiles)
    (anchor : ∀ N, DegreeTwoPairBinaryKernelAnchor
      (preE7PairAction 12 p ⧸ N.1)
      (profileOfState (realization.topNormalState N)
        (realization.moduleState N))) :
    DegreeTwoPairTopBinaryKernelRowData D
      degreeTwoTwelvePairExceptionalProfiles p realization :=
  ofProfileTable degreeTwoTwelvePairExceptionalProfiles
    degreeTwoTwelvePairExceptionalProfiles_capacity
    profileOfState profile_mem anchor

/-- Count-twelve joint-profile specialization. -/
noncomputable def twelveJointOfProfileTable
    {D : DegreeTwoPairTopFiniteInterface 12}
    {p : PreE7PairActionClass 12}
    {realization : DegreeTwoPairTopRealization D p}
    (kappa sectionCap : ℕ)
    (hparameters : (kappa, sectionCap) ∈
      degreeTwoTwelvePairJointParameters)
    (profileOfState : D.normalRegistry.State → D.ModuleState →
      DegreeTwoPairRelativeProfile)
    (profile_mem : ∀ N,
      profileOfState (realization.topNormalState N)
        (realization.moduleState N) ∈
          degreeTwoTwelvePairJointProfiles kappa sectionCap)
    (anchor : ∀ N, DegreeTwoPairBinaryKernelAnchor
      (preE7PairAction 12 p ⧸ N.1)
      (profileOfState (realization.topNormalState N)
        (realization.moduleState N))) :
    DegreeTwoPairTopBinaryKernelRowData D
      (degreeTwoTwelvePairJointProfiles kappa sectionCap) p realization :=
  ofProfileTable (degreeTwoTwelvePairJointProfiles kappa sectionCap)
    (degreeTwoTwelvePairJointProfiles_capacity kappa sectionCap hparameters)
    profileOfState profile_mem anchor

/-- Count-sixteen specialization. -/
noncomputable def sixteenOfProfileTable
    {D : DegreeTwoPairTopFiniteInterface 16}
    {p : PreE7PairActionClass 16}
    {realization : DegreeTwoPairTopRealization D p}
    (profileOfState : D.normalRegistry.State → D.ModuleState →
      DegreeTwoPairRelativeProfile)
    (profile_mem : ∀ N,
      profileOfState (realization.topNormalState N)
        (realization.moduleState N) ∈ degreeTwoSixteenPairProfiles)
    (anchor : ∀ N, DegreeTwoPairBinaryKernelAnchor
      (preE7PairAction 16 p ⧸ N.1)
      (profileOfState (realization.topNormalState N)
        (realization.moduleState N))) :
    DegreeTwoPairTopBinaryKernelRowData D
      degreeTwoSixteenPairProfiles p realization :=
  ofProfileTable degreeTwoSixteenPairProfiles
    degreeTwoSixteenPairProfiles_capacity profileOfState profile_mem anchor

noncomputable def twelveResolvedData
    {D : DegreeTwoPairTopFiniteInterface 12}
    {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
    {p : PreE7PairActionClass 12}
    {realization : DegreeTwoPairTopRealization D p}
    (A : DegreeTwoPairTopBinaryKernelRowData
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
    (A : DegreeTwoPairTopBinaryKernelRowData
      D expectedProfiles p realization)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeResolvedData D expectedProfiles p := by
  let lift := A.liftConclusion lit
  exact
    { lift := lift
      profiles_eq := A.liftConclusion_profiles_eq lit
      numerics := degreeTwoSixteenPairRelativeNumerics lift.lift }

end DegreeTwoPairTopBinaryKernelRowData

/-- Two-frame analogue for the paired-eight count-sixteen branch. -/
structure DegreeTwoPairTopTowerBinaryKernelRowData {s t : ℕ}
    (D : DegreeTwoPairTopFiniteInterface t)
    (expectedProfiles : Finset DegreeTwoPairRelativeProfile)
    (p : PreE7PairActionClass s)
    (realization : DegreeTwoPairTopTowerRealization D p) : Type 1 where
  stateProfile : DegreeTwoPairTopTowerStateProfile D p realization
  profiles_eq : stateProfile.allowedProfiles = expectedProfiles
  anchor : ∀ N, DegreeTwoPairBinaryKernelAnchor
    (preE7PairAction s p ⧸ N.1) (stateProfile.profile N)

namespace DegreeTwoPairTopTowerBinaryKernelRowData

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
  {p : PreE7PairActionClass s}
  {realization : DegreeTwoPairTopTowerRealization D p}
  (A : DegreeTwoPairTopTowerBinaryKernelRowData
    D expectedProfiles p realization)

noncomputable def liftConclusion (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeLiftConclusion D p := by
  let lift : DegreeTwoPairRelativeLiftData s p :=
    DegreeTwoPairRelativeLiftData.ofBinaryKernelAnchors lit
      A.stateProfile.profile A.stateProfile.capacity A.anchor
  exact
    { lift := lift
      topNormalState := realization.topNormalState
      moduleState := realization.moduleState
      profileOfState := A.stateProfile.profileOfState
      profile_eq := fun _ ↦ rfl
      allowedProfiles := A.stateProfile.allowedProfiles
      allowed_capacity := A.stateProfile.allowed_capacity
      profile_mem := A.stateProfile.profile_mem }

theorem liftConclusion_profiles_eq (lit : PreE7CharacterLiterature) :
    (A.liftConclusion lit).allowedProfiles = expectedProfiles := by
  change A.stateProfile.allowedProfiles = expectedProfiles
  exact A.profiles_eq

noncomputable def sixteenOfProfileTable
    {D : DegreeTwoPairTopFiniteInterface 8}
    {p : PreE7PairActionClass 16}
    {realization : DegreeTwoPairTopTowerRealization D p}
    (profileOfState : D.normalRegistry.State → D.ModuleState →
      DegreeTwoPairRelativeProfile)
    (profile_mem : ∀ N,
      profileOfState (realization.topNormalState N)
        (realization.moduleState N) ∈ degreeTwoSixteenPairProfiles)
    (anchor : ∀ N, DegreeTwoPairBinaryKernelAnchor
      (preE7PairAction 16 p ⧸ N.1)
      (profileOfState (realization.topNormalState N)
        (realization.moduleState N))) :
    DegreeTwoPairTopTowerBinaryKernelRowData D
      degreeTwoSixteenPairProfiles p realization :=
  { stateProfile :=
      { profileOfState := profileOfState
        allowedProfiles := degreeTwoSixteenPairProfiles
        allowed_capacity := degreeTwoSixteenPairProfiles_capacity
        profile_mem := profile_mem }
    profiles_eq := rfl
    anchor := anchor }

noncomputable def sixteenResolvedData
    {D : DegreeTwoPairTopFiniteInterface 8}
    {expectedProfiles : Finset DegreeTwoPairRelativeProfile}
    {p : PreE7PairActionClass 16}
    {realization : DegreeTwoPairTopTowerRealization D p}
    (A : DegreeTwoPairTopTowerBinaryKernelRowData
      D expectedProfiles p realization)
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairTopRelativeResolvedData D expectedProfiles p := by
  let lift := A.liftConclusion lit
  exact
    { lift := lift
      profiles_eq := A.liftConclusion_profiles_eq lit
      numerics := degreeTwoSixteenPairRelativeNumerics lift.lift }

end DegreeTwoPairTopTowerBinaryKernelRowData

/-- Resolve the count-twelve catalogue from actual binary-kernel anchors on
its relative rows and concrete QCHAR data on its ternary rows. -/
noncomputable def degreeTwoTwelveResolution_of_binaryKernel_and_ternary
    (lit : PreE7CharacterLiterature)
    (T : DegreeTwoTwelvePairTopFiniteCatalogue)
    (relative : ∀ (j : Fin 301) (p : PreE7PairActionClass 12)
      (realization : DegreeTwoPairTopRealization (T.row j).finite p),
      (T.row j).branch ≠ .ternary →
      DegreeTwoPairTopBinaryKernelRowData (T.row j).finite
        (T.row j).expectedProfiles p realization)
    (ternary : ∀ (j : Fin 301) (p : PreE7PairActionClass 12),
      DegreeTwoPairTopRealization (T.row j).finite p →
      (T.row j).branch = .ternary →
      DegreeTwoTwelveTernaryComparatorData p) :
    DegreeTwoTwelvePairTopCatalogueResolution T :=
  degreeTwoTwelveResolution_of_relative_and_ternary T
    (fun j p realization h ↦
      (relative j p realization h).twelveResolvedData lit)
    ternary

/-- Resolve all finite count-sixteen branches from binary-kernel anchors;
the two natural tops retain their uniform socle-generator theorem. -/
noncomputable def degreeTwoSixteenResolution_of_binaryKernel_and_naturalSocle
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (T : DegreeTwoSixteenPairTopFiniteCatalogue)
    (paired8 : ∀ (j : Fin 24) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopTowerRealization (T.paired8 j) p),
      DegreeTwoPairTopTowerBinaryKernelRowData (T.paired8 j)
        degreeTwoSixteenPairProfiles p realization)
    (zero16 : ∀ (j : Fin 29) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization (T.zero16 j) p),
      DegreeTwoPairTopBinaryKernelRowData (T.zero16 j)
        degreeTwoSixteenPairProfiles p realization)
    (twoAffine16 : ∀ (j : Fin 15) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization (T.twoAffine16 j) p),
      DegreeTwoPairTopBinaryKernelRowData (T.twoAffine16 j)
        degreeTwoSixteenPairProfiles p realization)
    (primitive16 : ∀ (j : Fin 20) (p : PreE7PairActionClass 16)
      (realization : DegreeTwoPairTopRealization (T.primitive16 j) p),
      DegreeTwoPairTopBinaryKernelRowData (T.primitive16 j)
        degreeTwoSixteenPairProfiles p realization)
    (natural : ∀ (kind : DegreeTwoSixteenNaturalTop)
      (p : PreE7PairActionClass 16)
      (realization : DegreeTwoSixteenNaturalTopRealization kind p),
      DegreeTwoSixteenNaturalSocleGeneratorData kind p realization) :
    DegreeTwoSixteenPairTopCatalogueResolution T where
  paired8 j p realization :=
    (paired8 j p realization).sixteenResolvedData lit |>.toResolvedRow
  zero16 j p realization :=
    (zero16 j p realization).sixteenResolvedData lit |>.toResolvedRow
  twoAffine16 j p realization :=
    (twoAffine16 j p realization).sixteenResolvedData lit |>.toResolvedRow
  primitive16 j p realization :=
    (primitive16 j p realization).sixteenResolvedData lit |>.toResolvedRow
  natural kind p realization :=
    (natural kind p realization).source hZmud lit

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
