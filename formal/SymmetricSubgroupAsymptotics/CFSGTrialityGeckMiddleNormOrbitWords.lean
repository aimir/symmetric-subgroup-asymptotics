import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleOrderedTensor
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTwistOperators
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedWordSimpleSigns

/-! Actual fixed word lifts of the cubic norm-curve orbit. The initial
root has an arbitrary literal fixed-field parameter; conjugation by the
actual short Frobenius word gives its scalar multiple of the norm curve.
The word remains in the SAME fixed middle radical, constructively. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleNormOrbitWords
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleRadicalCardinality CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeEdges CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckMiddleCubeEdgeOperators CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckMiddleTwistOperators CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckFixedPositiveRaw CFSGTrialityGeckFixedWordSimpleSigns
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckShortComplement
open CFSGTrialityGeckMatrixTwist CFSGTrialityFixedField CFSGSerreOrdinaryTwists
open CFSGGradedMatrixSubgroups CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixBlockProjection
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => CFSGTrialityD4NormTwo.D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem orderedOuterWord_eq_shortOrbit (K : Type) [Field K] (sigma : K ≃+* K) (t : K) :
    orderedOuterWord K t (sigma t) (sigma (sigma t)) = shortOrbit K sigma false t := by
  let u0 := outerWord K 0 t
  let u1 := outerWord K 1 (sigma t)
  let u2 := outerWord K 2 (sigma (sigma t))
  have h01 : Commute u0 u1 := CFSGTrialityGeckShortParameterWeyl.outer_roots_commute
    K 0 1 (by decide) false false t (sigma t)
  have h02 : Commute u0 u2 := CFSGTrialityGeckShortParameterWeyl.outer_roots_commute
    K 0 2 (by decide) false false t (sigma (sigma t))
  have h12 : Commute u1 u2 := CFSGTrialityGeckShortParameterWeyl.outer_roots_commute
    K 1 2 (by decide) false false (sigma t) (sigma (sigma t))
  change u2*(u1*u0) = (u0*u1)*u2
  calc
    _ = (u2*u1)*u0 := (mul_assoc _ _ _).symm
    _ = (u1*u2)*u0 := congrArg (fun z => z*u0) h12.eq.symm
    _ = u1*(u2*u0) := mul_assoc _ _ _
    _ = u1*(u0*u2) := congrArg (fun z => u1*z) h02.eq.symm
    _ = (u1*u0)*u2 := (mul_assoc _ _ _).symm
    _ = _ := congrArg (fun z => z*u2) h01.eq.symm

def normWord (q : CFSG.PrimePower) (t : q.Extension 3) : UnitsD4 (q.Extension 3) :=
  orderedOuterWord (q.Extension 3) t (t^q.order) (t^(q.order^2))

theorem normWord_eq_shortOrbit (q : CFSG.PrimePower) (t : q.Extension 3) :
    normWord q t = shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t := by
  have h2 : definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 t) = t^(q.order^2) := by
    change (t^q.order)^q.order = t^(q.order^2)
    rw [← pow_mul, pow_two]
  rw [normWord, ← h2]
  exact orderedOuterWord_eq_shortOrbit _ _ t

theorem normWord_mem_fixedPositive (q : CFSG.PrimePower) (t : q.Extension 3) :
    normWord q t ∈ fixedPositiveRaw q := by
  rw [normWord_eq_shortOrbit]
  exact shortOrbit_mem_fixedPositiveRaw q t

theorem zeroCube_word_sign : ∃ epsilon : ℤ, (epsilon=1 ∨ epsilon= -1) ∧
    ∀ (K : Type) [Field K] (b : K), cubeWord K zeroCube b =
      canonicalRoot rawData K false 1 ((epsilon:K)*b) := by
  obtain ⟨epsilon, hsign, hparam⟩ := selected_simple_root_sign A hd hs hp ho 1
  refine ⟨epsilon, hsign, ?_⟩
  intro K _ b
  have hroot : cubeRoot zeroCube = (CFSGTrialityD4NormTwo.Index 1 : CFSGNormTwoRootPairing.Roots A) := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  change CFSGNormTwoCoordinateSelectedRootElement.selectedRootElement A hd hs hp ho K
    (cubeRoot zeroCube) b = _
  rw [hroot]
  exact hparam K b

theorem zeroCube_mem_middle (K : Type) [Field K] (b : K) :
    cubeWord K zeroCube b ∈ middleRadical K :=
  middle_root_mem K (cubeRoot zeroCube) (cubeRoot_positive zeroCube)
    (by rw [cubeRoot_middle]) b

theorem zeroCube_fixed (q : CFSG.PrimePower) (b : fixedField q) :
    unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (cubeWord (q.Extension 3) zeroCube b.val) = cubeWord (q.Extension 3) zeroCube b.val := by
  obtain ⟨epsilon, _, hword⟩ := zeroCube_word_sign
  rw [hword, CFSGTrialityGeckRootSubgroupTwist.unitTwist_raw_root]
  have hb : definingFieldAutomorphism q 3 b.val = b.val := b.property
  simp only [map_mul, map_intCast, hb]
  rfl

theorem normWord_normalizes_middle (q : CFSG.PrimePower) (t : q.Extension 3) :
    normWord q t ∈ Subgroup.normalizer (middleRadical (q.Extension 3)) := by
  rw [middleRadical_eq_shortComplement]
  exact positive_le_normalizer_shortComplement _
    ((mem_fixedPositiveRaw_iff q _).mp (normWord_mem_fixedPositive q t)).1

def conjugateMiddleWord (q : CFSG.PrimePower) (b : fixedField q) (t : q.Extension 3) :
    UnitsD4 (q.Extension 3) :=
  normWord q t * cubeWord (q.Extension 3) zeroCube b.val * (normWord q t)⁻¹

theorem conjugateMiddleWord_mem_middle (q : CFSG.PrimePower) (b : fixedField q) (t : q.Extension 3) :
    conjugateMiddleWord q b t ∈ middleRadical (q.Extension 3) :=
  (Subgroup.mem_normalizer_iff.mp (normWord_normalizes_middle q t) _).mp (zeroCube_mem_middle _ _)

theorem conjugateMiddleWord_fixed (q : CFSG.PrimePower) (b : fixedField q) (t : q.Extension 3) :
    unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) (conjugateMiddleWord q b t) =
      conjugateMiddleWord q b t := by
  have hg := ((mem_fixedPositiveRaw_iff q _).mp (normWord_mem_fixedPositive q t)).2
  simp only [conjugateMiddleWord, map_mul, map_inv, hg, zeroCube_fixed]

theorem conjugateMiddleWord_firstLayer (q : CFSG.PrimePower) (b : fixedField q) (t : q.Extension 3) :
    firstLayer middleWeight (conjugateMiddleWord q b t) =
      b.val • normOrbit (q.Extension 3) q.order t := by
  have hg : normWord q t ∈ preservingUnits middleWeight :=
    (preservingUnits middleWeight).mul_mem (outerWord_preserving _ 2 _)
      ((preservingUnits middleWeight).mul_mem (outerWord_preserving _ 1 _)
        (outerWord_preserving _ 0 _))
  rw [conjugateMiddleWord, firstLayer_conjugate _ middleWeight _ _ hg
    ((preservingUnits middleWeight).inv_mem hg), cubeWord_firstLayer]
  change CFSGAlgebraConjugationAction.action (q.Extension 3) (Mat (q.Extension 3))
    (normWord q t) (b.val • cubeCoefficient (q.Extension 3) zeroCube) = _
  rw [map_smul]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleNormOrbitWords
