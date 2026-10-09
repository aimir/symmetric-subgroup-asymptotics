import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairRelativeCharacterEnvelope
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

end DegreeTwoPairTopStateProfile

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
