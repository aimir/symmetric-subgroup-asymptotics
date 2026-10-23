import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeSpanActions
import SymmetricSubgroupAsymptotics.CFSGOrderedCubeNormOrbitSpan

/-! Binary reindexing of the actual signed middle-root tensor basis and
its ordered outer-word action. The norm-curve span here is over the
EXTENSION field. No base-field fixed-space or derived-group conclusion
is inferred from that span. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeEdges CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckMiddleCubeEdgeOperators CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleCubeSpanActions CFSGOrderedCubeOperatorExpansion
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def cubeBits (i : Fin 8) : Cube :=
  match i.val with
  | 0 => ![0,0,0]
  | 1 => ![1,0,0]
  | 2 => ![0,1,0]
  | 3 => ![1,1,0]
  | 4 => ![0,0,1]
  | 5 => ![1,0,1]
  | 6 => ![0,1,1]
  | _ => ![1,1,1]

theorem cubeBits_bijective : Function.Bijective cubeBits := by decide

def cubeBitsEquiv : Fin 8 ≃ Cube := Equiv.ofBijective cubeBits cubeBits_bijective

theorem tensorWord_eq (K : Type) [Field K] (i : Fin 8) :
    tensorWord (edgeShift K 0) (edgeShift K 1) (edgeShift K 2)
      (cubeCoefficient K zeroCube) i = tensorBasis K (cubeBits i) := by
  fin_cases i <;>
    simp [tensorWord, tensorBasis, tensorStage, cubeBits, zeroCube]

theorem tensorWord_linearIndependent (K : Type) [Field K] :
    LinearIndependent K (tensorWord (edgeShift K 0) (edgeShift K 1) (edgeShift K 2)
      (cubeCoefficient K zeroCube)) := by
  have h := (tensorBasis_linearIndependent K).comp cubeBits cubeBits_bijective.1
  have hfun : tensorWord (edgeShift K 0) (edgeShift K 1) (edgeShift K 2)
      (cubeCoefficient K zeroCube) = fun i => tensorBasis K (cubeBits i) :=
    funext (tensorWord_eq K)
  rw [hfun]
  exact h

def orderedOuterWord (K : Type) [Field K] (a b c : K) : UnitsD4 K :=
  outerWord K 2 c * (outerWord K 1 b * outerWord K 0 a)

theorem orderedOuterWord_action (K : Type) [Field K] (a b c : K) (M : Mat K)
    (hM : M ∈ cubeSpan K) :
    CFSGAlgebraConjugationAction.action K (Mat K) (orderedOuterWord K a b c) M =
      orderedAction (edgeShift K 0) (edgeShift K 1) (edgeShift K 2) M a b c := by
  have h0 : outerLinear K 0 a M ∈ cubeSpan K := by
    rw [outerLinear_on_cubeSpan K 0 a M hM]
    exact Submodule.add_mem _ hM
      (Submodule.smul_mem _ a (edgeShift_mem_cubeSpan K 0 M hM))
  have h1 : outerLinear K 1 b (outerLinear K 0 a M) ∈ cubeSpan K := by
    rw [outerLinear_on_cubeSpan K 1 b _ h0]
    exact Submodule.add_mem _ h0
      (Submodule.smul_mem _ b (edgeShift_mem_cubeSpan K 1 _ h0))
  simp only [orderedOuterWord, map_mul, LinearEquiv.mul_apply]
  change outerLinear K 2 c (outerLinear K 1 b (outerLinear K 0 a M)) = _
  rw [outerLinear_on_cubeSpan K 2 c _ h1,
    outerLinear_on_cubeSpan K 1 b _ h0, outerLinear_on_cubeSpan K 0 a M hM]
  rfl

def normOrbit (K : Type) [Field K] (q : ℕ) (t : K) : Mat K :=
  CFSGAlgebraConjugationAction.action K (Mat K)
    (orderedOuterWord K t (t^q) (t^(q^2))) (cubeCoefficient K zeroCube)

theorem normOrbit_expansion (K : Type) [Field K] (q : ℕ) (t : K) :
    normOrbit K q t = ∑ i : Fin 8,
      CFSGCubicNormMonomialSeparation.normCurve q t i • tensorBasis K (cubeBits i) := by
  rw [normOrbit, orderedOuterWord_action K _ _ _ _
    (Submodule.subset_span (Set.mem_range_self zeroCube)), orderedAction_expansion,
    cubeParameters_eq_normCurve]
  simp only [tensorWord_eq]

theorem normOrbit_span (K : Type) [Field K] [Finite K]
    (q : ℕ) (hq : 2 ≤ q) (hcard : Nat.card K = q^3) :
    Submodule.span K (Set.range (normOrbit K q)) = cubeSpan K := by
  have hfun : normOrbit K q = fun t : K =>
      orderedAction (edgeShift K 0) (edgeShift K 1) (edgeShift K 2)
        (cubeCoefficient K zeroCube) t (t^q) (t^(q^2)) := by
    funext t
    exact orderedOuterWord_action K _ _ _ _
      (Submodule.subset_span (Set.mem_range_self zeroCube))
  rw [hfun, CFSGOrderedCubeNormOrbitSpan.ordered_orbit_span _ _ _ _ q hq hcard]
  have hrange : Set.range (tensorWord (edgeShift K 0) (edgeShift K 1) (edgeShift K 2)
      (cubeCoefficient K zeroCube)) = Set.range (tensorBasis K) := by
    ext M
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨cubeBits i, (tensorWord_eq K i).symm⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨i, rfl⟩ := cubeBits_bijective.2 a
      exact ⟨i, tensorWord_eq K i⟩
  rw [hrange, span_tensorBasis_eq]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleOrderedTensor
