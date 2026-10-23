import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleNormOrbitWords
import SymmetricSubgroupAsymptotics.CFSGHomDerivedRange

/-! Fixed conjugates and fixed commutators in the SAME actual positive
matrix group. Their first layers are respectively scalar norm-orbit
vectors and scalar differences from the initial root coefficient.
All subgroup memberships are literal, including the derived image. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
open scoped commutatorElement
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleRadicalCardinality CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeEdges CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckMiddleSignedTensorBasis CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckMiddleNormOrbitWords CFSGTrialityGeckMiddleTwistOperators
open CFSGTrialityGeckFixedPositiveRaw CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckMatrixTwist CFSGTrialityFixedField CFSGSerreOrdinaryTwists
open CFSGGradedMatrixGroupFirstLayer CFSGHomDerivedRange
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem middle_le_positive (K : Type) [Field K] : middleRadical K ≤ Positive K := by
  rw [middleRadical_eq_shortComplement]
  exact CFSGTrialityGeckShortComplement.shortComplement_le_positive K

theorem zeroCube_mem_fixedPositive (q : CFSG.PrimePower) (b : fixedField q) :
    cubeWord (q.Extension 3) zeroCube b.val ∈ fixedPositiveRaw q :=
  (mem_fixedPositiveRaw_iff q _).mpr
    ⟨middle_le_positive _ (zeroCube_mem_middle _ _), zeroCube_fixed q b⟩

def fixedMiddle (q : CFSG.PrimePower) : Subgroup (Raw (q.Extension 3)) :=
  middleRadical (q.Extension 3) ⊓ fixedPositiveRaw q

def fixedMiddleFirstLayerHom (q : CFSG.PrimePower) :
    fixedMiddle q →* Multiplicative (Mat (q.Extension 3)) :=
  (middleFirstLayerHom (q.Extension 3)).comp (Subgroup.inclusion inf_le_left)

theorem conjugateMiddleWord_mem_fixedMiddle (q : CFSG.PrimePower)
    (b : fixedField q) (t : q.Extension 3) : conjugateMiddleWord q b t ∈ fixedMiddle q := by
  refine ⟨conjugateMiddleWord_mem_middle q b t, ?_⟩
  exact (fixedPositiveRaw q).mul_mem
    ((fixedPositiveRaw q).mul_mem (normWord_mem_fixedPositive q t) (zeroCube_mem_fixedPositive q b))
    ((fixedPositiveRaw q).inv_mem (normWord_mem_fixedPositive q t))

def positiveDerived (q : CFSG.PrimePower) : Subgroup (Raw (q.Extension 3)) :=
  (derivedMap (fixedPositiveRaw q).subtype).range

def derivedMiddle (q : CFSG.PrimePower) : Subgroup (Raw (q.Extension 3)) :=
  middleRadical (q.Extension 3) ⊓ positiveDerived q

def derivedMiddleFirstLayerHom (q : CFSG.PrimePower) :
    derivedMiddle q →* Multiplicative (Mat (q.Extension 3)) :=
  (middleFirstLayerHom (q.Extension 3)).comp (Subgroup.inclusion inf_le_left)

def commutatorMiddleWord (q : CFSG.PrimePower) (b : fixedField q) (t : q.Extension 3) :
    Raw (q.Extension 3) :=
  conjugateMiddleWord q b t * (cubeWord (q.Extension 3) zeroCube b.val)⁻¹

theorem commutatorMiddleWord_mem_middle (q : CFSG.PrimePower) (b : fixedField q) (t : q.Extension 3) :
    commutatorMiddleWord q b t ∈ middleRadical (q.Extension 3) :=
  (middleRadical _).mul_mem (conjugateMiddleWord_mem_middle q b t)
    ((middleRadical _).inv_mem (zeroCube_mem_middle _ _))

theorem commutatorMiddleWord_mem_derived (q : CFSG.PrimePower) (b : fixedField q) (t : q.Extension 3) :
    commutatorMiddleWord q b t ∈ positiveDerived q := by
  let g : fixedPositiveRaw q := ⟨normWord q t, normWord_mem_fixedPositive q t⟩
  let x : fixedPositiveRaw q := ⟨cubeWord (q.Extension 3) zeroCube b.val, zeroCube_mem_fixedPositive q b⟩
  exact CFSGHomDerivedRange.commutator_mem (fixedPositiveRaw q).subtype g x

theorem commutatorMiddleWord_mem_derivedMiddle (q : CFSG.PrimePower)
    (b : fixedField q) (t : q.Extension 3) : commutatorMiddleWord q b t ∈ derivedMiddle q :=
  ⟨commutatorMiddleWord_mem_middle q b t, commutatorMiddleWord_mem_derived q b t⟩

theorem commutatorMiddleWord_firstLayer (q : CFSG.PrimePower) (b : fixedField q) (t : q.Extension 3) :
    firstLayer middleWeight (commutatorMiddleWord q b t) =
      b.val • (normOrbit (q.Extension 3) q.order t - cubeCoefficient (q.Extension 3) zeroCube) := by
  rw [commutatorMiddleWord, firstLayer_mul middleWeight _ _
    (middle_le_strict _ (conjugateMiddleWord_mem_middle q b t))
      ((CFSGGradedMatrixSubgroups.strictUnits middleWeight).inv_mem (cubeWord_strict _ _ _)),
    conjugateMiddleWord_firstLayer, firstLayer_inv middleWeight _ (cubeWord_strict _ _ _),
    cubeWord_firstLayer, smul_sub]
  simp only [sub_eq_add_neg]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
