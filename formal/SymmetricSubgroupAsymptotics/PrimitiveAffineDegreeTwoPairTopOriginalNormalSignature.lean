import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRelativeKernelAnchor
import SymmetricSubgroupAsymptotics.BinaryPairSharedBinding

/-!
# Original-normal signatures for pair-top catalogues

The pair-top files enumerate normal subgroups of the top action and invariant
submodules of its natural binary permutation module.  The objects to be
bounded, however, are normal subgroups of the original two-point-block
action.  This file makes the semantic connection.

For every literal original normal `N`, its image in the top is pulled back
through the catalogue equivalence, and its intersection with the pair kernel
is transported to the catalogue permutation module.  Completeness of the two
finite registries then selects the unique emitted states.  The final
constructor combines those states with kernel-determining relative labels and
produces `DegreeTwoPairTopRelativeLiftConclusion` on every original normal.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- A finite pair top reached through two successive pair frames.  This is
the semantic shape of the count-sixteen paired-eight rows: an original
sixteen-pair normal is first mapped to the outer top, then that normal is
mapped through the eight-pair frame before the finite registries are read. -/
structure DegreeTwoPairTopTowerRealization {s t : ℕ}
    (D : DegreeTwoPairTopFiniteInterface t)
    (p : PreE7PairActionClass s) : Type 1 where
  frame : BinaryPairFrame (preE7PairAction s p) (Fin s)
  secondFrame : BinaryPairFrame frame.top.range (Fin t)
  topEquiv : D.top ≃* secondFrame.top.range
  module_action_eq : ∀ g v,
    permutationFunctionRepresentation (ZMod 2) D.top (Fin t) g v =
      secondFrame.coordinateTopAction (topEquiv g) v

namespace DegreeTwoPairTopRealization

variable {s : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopRealization D p)

/-- The actual top image of one original normal, expressed in the literal
catalogue top by the realization equivalence. -/
def topNormal (N : Subgroup (preE7PairAction s p)) : Subgroup D.top :=
  (N.map R.frame.top.rangeRestrict).comap R.topEquiv.toMonoidHom

theorem topNormal_normal (N : Subgroup (preE7PairAction s p)) [N.Normal] :
    (R.topNormal N).Normal := by
  apply Subgroup.Normal.comap
  exact Subgroup.Normal.map inferInstance _
    R.frame.top.rangeRestrict_surjective

/-- The literal normal axis attached to an original normal. -/
def topNormalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    {T : Subgroup D.top // T.Normal} := by
  letI : N.1.Normal := N.2
  exact ⟨R.topNormal N.1, R.topNormal_normal N.1⟩

/-- The unique emitted top-normal state of an original normal. -/
noncomputable def topNormalState
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.normalRegistry.State :=
  D.normalRegistry.normalAxisEquiv.symm (R.topNormalAxis N)

theorem topNormalState_spec
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.normalRegistry.state (R.topNormalState N) = R.topNormal N.1 := by
  have h := D.normalRegistry.normalAxisEquiv.apply_symm_apply
    (R.topNormalAxis N)
  exact congrArg Subtype.val h

/-- The actual intersection of an original normal with the pair kernel,
viewed in the literal catalogue permutation module. -/
def moduleAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin s)) := by
  letI : N.1.Normal := N.2
  exact R.frame.sharedOriginalAxis
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin s))
    R.topEquiv R.module_action_eq N.1

/-- The unique emitted invariant-module state of an original normal. -/
noncomputable def moduleState
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.ModuleState :=
  D.moduleStateEquiv.symm (R.moduleAxis N)

theorem moduleState_spec
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.moduleState (R.moduleState N) = R.moduleAxis N :=
  D.moduleStateEquiv.apply_symm_apply (R.moduleAxis N)

end DegreeTwoPairTopRealization

namespace DegreeTwoPairTopTowerRealization

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  (R : DegreeTwoPairTopTowerRealization D p)

/-- The image of an original normal in the first pair top. -/
def outerTopNormal
    (N : Subgroup (preE7PairAction s p)) : Subgroup R.frame.top.range :=
  N.map R.frame.top.rangeRestrict

theorem outerTopNormal_normal
    (N : Subgroup (preE7PairAction s p)) [N.Normal] :
    (R.outerTopNormal N).Normal :=
  Subgroup.Normal.map inferInstance _ R.frame.top.rangeRestrict_surjective

/-- The image in the second pair top, transported to the literal catalogue
top. -/
def topNormal
    (N : Subgroup (preE7PairAction s p)) : Subgroup D.top :=
  ((R.outerTopNormal N).map R.secondFrame.top.rangeRestrict).comap
    R.topEquiv.toMonoidHom

theorem topNormal_normal
    (N : Subgroup (preE7PairAction s p)) [N.Normal] :
    (R.topNormal N).Normal := by
  letI : (R.outerTopNormal N).Normal := R.outerTopNormal_normal N
  apply Subgroup.Normal.comap
  exact Subgroup.Normal.map inferInstance _
    R.secondFrame.top.rangeRestrict_surjective

def topNormalAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    {T : Subgroup D.top // T.Normal} := by
  letI : N.1.Normal := N.2
  exact ⟨R.topNormal N.1, R.topNormal_normal N.1⟩

/-- The unique finite top-normal state selected after both pair maps. -/
noncomputable def topNormalState
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.normalRegistry.State :=
  D.normalRegistry.normalAxisEquiv.symm (R.topNormalAxis N)

theorem topNormalState_spec
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.normalRegistry.state (R.topNormalState N) = R.topNormal N.1 := by
  have h := D.normalRegistry.normalAxisEquiv.apply_symm_apply
    (R.topNormalAxis N)
  exact congrArg Subtype.val h

/-- The intersection of the first top image with the second pair kernel,
transported to the literal eight-coordinate permutation module. -/
def moduleAxis
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) D.top (Fin t)) := by
  letI : N.1.Normal := N.2
  letI : (R.outerTopNormal N.1).Normal := R.outerTopNormal_normal N.1
  exact R.secondFrame.sharedOriginalAxis
    (permutationFunctionRepresentation (ZMod 2) D.top (Fin t))
    R.topEquiv R.module_action_eq (R.outerTopNormal N.1)

/-- The unique finite module state selected after both pair maps. -/
noncomputable def moduleState
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.ModuleState :=
  D.moduleStateEquiv.symm (R.moduleAxis N)

theorem moduleState_spec
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    D.moduleState (R.moduleState N) = R.moduleAxis N :=
  D.moduleStateEquiv.apply_symm_apply (R.moduleAxis N)

end DegreeTwoPairTopTowerRealization

/-- A profile table on the two independently complete finite registries.
The `profile_mem` proof is checked only after the actual original-normal
signature has selected its two states. -/
structure DegreeTwoPairTopStateProfile {s : ℕ}
    (D : DegreeTwoPairTopFiniteInterface s)
    (p : PreE7PairActionClass s)
    (R : DegreeTwoPairTopRealization D p) : Type where
  profileOfState : D.normalRegistry.State → D.ModuleState →
    DegreeTwoPairRelativeProfile
  allowedProfiles : Finset DegreeTwoPairRelativeProfile
  allowed_capacity : ∀ profile ∈ allowedProfiles,
    profile.slope ≤ preE7CharacterWindow (2 * s)
  profile_mem : ∀ N,
    profileOfState (R.topNormalState N) (R.moduleState N) ∈
      allowedProfiles

namespace DegreeTwoPairTopStateProfile

variable {s : ℕ} {D : DegreeTwoPairTopFiniteInterface s}
  {p : PreE7PairActionClass s}
  {R : DegreeTwoPairTopRealization D p}
  (P : DegreeTwoPairTopStateProfile D p R)

/-- The exact profile selected for a literal original normal. -/
def profile
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    DegreeTwoPairRelativeProfile :=
  P.profileOfState (R.topNormalState N) (R.moduleState N)

theorem capacity
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (P.profile N).slope ≤ preE7CharacterWindow (2 * s) :=
  P.allowed_capacity _ (P.profile_mem N)

/-- Complete the universal pair-relative lift from a kernel-determining
mixed label on each actual original quotient.  The finite normal and module
states in the conclusion are constructed here from `N`; callers do not
supply an unverified lookup from original normals into the catalogue. -/
noncomputable def relativeLiftConclusion
    (certificate : ∀ N,
      DegreeTwoPairRelativeLabelCertificate
        (preE7PairAction s p ⨸ N.1) (P.profile N)) :
    DegreeTwoPairTopRelativeLiftConclusion D p := by
  let lift : DegreeTwoPairRelativeLiftData s p :=
    DegreeTwoPairRelativeLiftData.ofLabelCertificates
      P.profile P.capacity certificate
  exact
    { lift := lift
      topNormalState := R.topNormalState
      moduleState := R.moduleState
      profileOfState := P.profileOfState
      profile_eq := fun _ => rfl
      allowedProfiles := P.allowedProfiles
      allowed_capacity := P.allowed_capacity
      profile_mem := P.profile_mem }

/-- Complete the universal pair-relative lift from the actual anchored
character construction on each original quotient.  This is the direct
semantic route used by the finite pair-top registries: their two states
select the profile, while the anchored data supplies the source-dependent
restriction label and its kernel theorem. -/
noncomputable def relativeAnchorLiftConclusion
    (lit : PreE7CharacterLiterature)
    (data : ∀ N,
      DegreeTwoPairRelativeAnchorLabels
        (preE7PairAction s p ⨸ N.1) (P.profile N)) :
    DegreeTwoPairTopRelativeLiftConclusion D p := by
  let lift : DegreeTwoPairRelativeLiftData s p :=
    DegreeTwoPairRelativeLiftData.ofRelativeAnchorLabels
      lit P.profile P.capacity data
  exact
    { lift := lift
      topNormalState := R.topNormalState
      moduleState := R.moduleState
      profileOfState := P.profileOfState
      profile_eq := fun _ => rfl
      allowedProfiles := P.allowedProfiles
      allowed_capacity := P.allowed_capacity
      profile_mem := P.profile_mem }

/-- Complete the universal pair-relative lift from a fixed prefix, actual
relative target irreducibles, and one chosen normal constituent per tail
slot.  The Sylow labels and their kernel theorem are constructed by
`DegreeTwoPairRelativeKernelAnchor.toQuotientEnvelope`. -/
noncomputable def relativeKernelLiftConclusion
    (lit : PreE7CharacterLiterature)
    (data : ∀ N,
      DegreeTwoPairRelativeKernelAnchor
        (preE7PairAction s p ⨸ N.1) (P.profile N)) :
    DegreeTwoPairTopRelativeLiftConclusion D p := by
  let lift : DegreeTwoPairRelativeLiftData s p :=
    DegreeTwoPairRelativeLiftData.ofRelativeKernelAnchors
      lit P.profile P.capacity data
  exact
    { lift := lift
      topNormalState := R.topNormalState
      moduleState := R.moduleState
      profileOfState := P.profileOfState
      profile_eq := fun _ ↦ rfl
      allowedProfiles := P.allowedProfiles
      allowed_capacity := P.allowed_capacity
      profile_mem := P.profile_mem }

end DegreeTwoPairTopStateProfile

/-- A profile table for a finite top reached through two pair frames.  It is
the tower analogue of `DegreeTwoPairTopStateProfile` and keeps every profile
attached to the actual original normal rather than to an independently
chosen catalogue state. -/
structure DegreeTwoPairTopTowerStateProfile {s t : ℕ}
    (D : DegreeTwoPairTopFiniteInterface t)
    (p : PreE7PairActionClass s)
    (R : DegreeTwoPairTopTowerRealization D p) : Type where
  profileOfState : D.normalRegistry.State → D.ModuleState →
    DegreeTwoPairRelativeProfile
  allowedProfiles : Finset DegreeTwoPairRelativeProfile
  allowed_capacity : ∀ profile ∈ allowedProfiles,
    profile.slope ≤ preE7CharacterWindow (2 * s)
  profile_mem : ∀ N,
    profileOfState (R.topNormalState N) (R.moduleState N) ∈
      allowedProfiles

namespace DegreeTwoPairTopTowerStateProfile

variable {s t : ℕ} {D : DegreeTwoPairTopFiniteInterface t}
  {p : PreE7PairActionClass s}
  {R : DegreeTwoPairTopTowerRealization D p}
  (P : DegreeTwoPairTopTowerStateProfile D p R)

def profile
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    DegreeTwoPairRelativeProfile :=
  P.profileOfState (R.topNormalState N) (R.moduleState N)

theorem capacity
    (N : {N : Subgroup (preE7PairAction s p) // N.Normal}) :
    (P.profile N).slope ≤ preE7CharacterWindow (2 * s) :=
  P.allowed_capacity _ (P.profile_mem N)

/-- Direct tower-row lift from actual anchored labels on every original
quotient. -/
noncomputable def relativeAnchorLiftConclusion
    (lit : PreE7CharacterLiterature)
    (data : ∀ N,
      DegreeTwoPairRelativeAnchorLabels
        (preE7PairAction s p ⨸ N.1) (P.profile N)) :
    DegreeTwoPairTopRelativeLiftConclusion D p := by
  let lift : DegreeTwoPairRelativeLiftData s p :=
    DegreeTwoPairRelativeLiftData.ofRelativeAnchorLabels
      lit P.profile P.capacity data
  exact
    { lift := lift
      topNormalState := R.topNormalState
      moduleState := R.moduleState
      profileOfState := P.profileOfState
      profile_eq := fun _ => rfl
      allowedProfiles := P.allowedProfiles
      allowed_capacity := P.allowed_capacity
      profile_mem := P.profile_mem }

/-- Tower-row form of `relativeKernelLiftConclusion`. -/
noncomputable def relativeKernelLiftConclusion
    (lit : PreE7CharacterLiterature)
    (data : ∀ N,
      DegreeTwoPairRelativeKernelAnchor
        (preE7PairAction s p ⨸ N.1) (P.profile N)) :
    DegreeTwoPairTopRelativeLiftConclusion D p := by
  let lift : DegreeTwoPairRelativeLiftData s p :=
    DegreeTwoPairRelativeLiftData.ofRelativeKernelAnchors
      lit P.profile P.capacity data
  exact
    { lift := lift
      topNormalState := R.topNormalState
      moduleState := R.moduleState
      profileOfState := P.profileOfState
      profile_eq := fun _ ↦ rfl
      allowedProfiles := P.allowedProfiles
      allowed_capacity := P.allowed_capacity
      profile_mem := P.profile_mem }

end DegreeTwoPairTopTowerStateProfile

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
