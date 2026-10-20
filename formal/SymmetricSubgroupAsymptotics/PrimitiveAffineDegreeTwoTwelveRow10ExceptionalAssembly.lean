import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10OriginalGeometry
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopConcreteBranches

/-!
# Complete relative data for the literal exceptional row 10

The existing top-normal state selects between the binary normalizer branch
and the nonbinary `S₃` branch. Both branches retain each actual original
normal quotient. No module multiplicity, central-rank, quotient census,
or new character-feasibility input remains.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10ExceptionalAssembly

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoTwelveRow10OriginalGeometry

abbrev rowInterface := DegreeTwoTwelvePairFiniteCatalogue.row10Interface

variable {p : PreE7PairActionClass 12}
  (R : DegreeTwoPairTopRealization rowInterface p)

/-- The profile depends on the existing top-normal state alone. The
module state is unnecessary for this geometric row. -/
def profileOfState (i : rowInterface.normalRegistry.State)
    (_ : rowInterface.ModuleState) : DegreeTwoPairRelativeProfile :=
  if IsPGroup 2 (rowInterface.top ⧸ rowInterface.normalRegistry.state i) then
    degreeTwoPairRelativeProfile 1 0 0 4
  else degreeTwoPairRelativeProfile 0 0 1 3

theorem profileOfState_mem (i : rowInterface.normalRegistry.State)
    (j : rowInterface.ModuleState) :
    profileOfState i j ∈ degreeTwoTwelvePairExceptionalProfiles := by
  unfold profileOfState
  split <;> simp [degreeTwoTwelvePairExceptionalProfiles]

def stateProfile : DegreeTwoPairTopStateProfile rowInterface p R where
  profileOfState := profileOfState
  allowedProfiles := degreeTwoTwelvePairExceptionalProfiles
  allowed_capacity := degreeTwoTwelvePairExceptionalProfiles_capacity
  profile_mem N := profileOfState_mem (R.topNormalState N) (R.moduleState N)

/-- Each original normal is handled by its actual top quotient. Binaryity
descends through the original quotient map, so the second case really is
a nonbinary original quotient. -/
noncomputable def quotientAnchor (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}) :
    DegreeTwoPairRelativeKernelAnchor (preE7PairAction 12 p ⧸ N.1)
      ((stateProfile R).profile N) := by
  letI : N.1.Normal := N.2
  change DegreeTwoPairRelativeKernelAnchor (preE7PairAction 12 p ⧸ N.1)
    (profileOfState (R.topNormalState N) (R.moduleState N))
  unfold profileOfState
  split
  · rename_i hbinaryTop
    exact (Classical.choice
      (PrimitiveAffineDegreeTwoTwelveRow10NormalizerPrefix.binary_top_quotient_orbitInput
        R N hbinaryTop)).anchor
  · rename_i hnonbinaryTop
    have hQ : ¬ IsPGroup 2 (preE7PairAction 12 p ⧸ N.1) := by
      intro hQ
      exact hnonbinaryTop
        (hQ.of_surjective (R.quotientMap N) (R.quotientMap_surjective N))
    exact nonbinary_quotient_anchor R hZmud N hQ

/-- Universal lift data for literal row 10, with the prescribed exceptional
profile menu and the actual original-normal signature. -/
noncomputable def liftConclusion (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    DegreeTwoPairTopRelativeLiftConclusion rowInterface p :=
  (stateProfile R).relativeKernelLiftConclusion lit (quotientAnchor R hZmud)

theorem liftConclusion_profiles_eq (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (liftConclusion R lit hZmud).allowedProfiles =
      degreeTwoTwelvePairExceptionalProfiles := rfl

/-- This is the complete row payload accepted by the count-twelve
catalogue resolver. The only external inputs are its existing literature
inputs and the published whole-socle Zmud theorem. -/
noncomputable def resolvedData (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    DegreeTwoPairTopRelativeResolvedData rowInterface
      degreeTwoTwelvePairExceptionalProfiles p :=
  { lift := liftConclusion R lit hZmud
    profiles_eq := liftConclusion_profiles_eq R lit hZmud
    numerics := degreeTwoTwelvePairRelativeNumerics (liftConclusion R lit hZmud).lift }

noncomputable def resolvedRow (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    DegreeTwoPairTopResolvedRow rowInterface degreeTwoTwelvePairExceptionalProfiles p :=
  (resolvedData R lit hZmud).toResolvedRow

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10ExceptionalAssembly

end
