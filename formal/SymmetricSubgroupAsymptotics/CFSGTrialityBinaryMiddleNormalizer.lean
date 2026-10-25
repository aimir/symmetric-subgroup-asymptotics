import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeRootGenerated
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A literal normalizer inside the actual fixed-root-generated source.
It contains the same fixed middle radical, the actual short positive
parameters, and the actual short Weyl word. Thus every displayed action
retains the original-model projection provenance. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleNormalizer
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFixedCommutators
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleNormOrbitWords
open CFSGTrialityGeckMiddleRadicalCardinality CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortComplement
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckMatrixTwist CFSGCentralTwistedCommutatorLift CFSGSerreOrdinaryTwists
local instance trialityMiddleNormalizerRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

theorem fixedMiddle_eq_inf_fixed (q : CFSG.PrimePower) :
    fixedMiddle q=middleRadical (q.Extension 3) ⊓
      fixedSubgroup (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)) := by
  ext u
  constructor
  · intro h
    exact ⟨h.1,((mem_fixedPositiveRaw_iff q u).mp h.2).2⟩
  · rintro ⟨hm,hf⟩
    exact ⟨hm,(mem_fixedPositiveRaw_iff q u).mpr ⟨middle_le_positive _ hm,hf⟩⟩

private theorem normalizes_fixedMiddle (q : CFSG.PrimePower)
    (g : Raw (q.Extension 3))
    (hm : g ∈ Subgroup.normalizer (middleRadical (q.Extension 3)))
    (hf : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) g=g) :
    g ∈ Subgroup.normalizer (fixedMiddle q) := by
  rw [fixedMiddle_eq_inf_fixed]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hm,(fixedSubgroup (unitTwist (q.Extension 3)
      (definingFieldAutomorphism q 3))).le_normalizer hf⟩

def carrier (q : CFSG.PrimePower) : Subgroup (Raw (q.Extension 3)) :=
  Subgroup.normalizer (fixedMiddle q) ⊓
    fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)

theorem middle_le_carrier (q : CFSG.PrimePower) : fixedMiddle q ≤ carrier q := by
  intro u hu
  refine ⟨(fixedMiddle q).le_normalizer hu,?_⟩
  exact signedFixed_le_generated _ _ false ((mem_fixedPositiveRaw_iff q u).mp hu.2)

def conjugationAction (q : CFSG.PrimePower) : carrier q →* MulAut (fixedMiddle q) :=
  (fixedMiddle q).normalizerMonoidHom.comp (Subgroup.inclusion inf_le_left)

theorem conjugationAction_val (q : CFSG.PrimePower) (g : carrier q) (u : fixedMiddle q) :
    (conjugationAction q g u).val=g.val*u.val*g.val⁻¹ := rfl

def positiveElement (q : CFSG.PrimePower) (a : q.Extension 3) : carrier q :=
  ⟨normWord q a,by
    refine ⟨normalizes_fixedMiddle q _ (normWord_normalizes_middle q a)
      (((mem_fixedPositiveRaw_iff q _).mp (normWord_mem_fixedPositive q a)).2),?_⟩
    rw [normWord_eq_shortOrbit]
    exact shortOrbit_mem_generated _ _ false a
      (CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q a)⟩

theorem positiveElement_val (q : CFSG.PrimePower) (a : q.Extension 3) :
    (positiveElement q a).val=normWord q a := rfl

def weylElement (q : CFSG.PrimePower) : carrier q :=
  ⟨shortWeyl (q.Extension 3),by
    refine ⟨normalizes_fixedMiddle q _ ?_ (shortWeyl_fixed _ _),
      shortWeyl_mem_generated _ _⟩
    rw [middleRadical_eq_shortComplement]
    exact shortWeyl_mem_normalizer_shortComplement _⟩

theorem weylElement_val (q : CFSG.PrimePower) :
    (weylElement q).val=shortWeyl (q.Extension 3) := rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleNormalizer
