import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleSignedTensorBasis

/-! The actual outer conjugations are id+tN on the eight-root span.
The edge operators commute because the original three outer root words
commute. Their ordered signed tensor words span exactly this same space.
No square-zero assertion outside this space is made. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeSpanActions
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeEdges CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckMiddleCubeEdgeOperators CFSGTrialityGeckMiddleSignedTensorBasis
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def cubeSpan (K : Type) [Field K] : Submodule K (Mat K) :=
  Submodule.span K (Set.range (cubeCoefficient K))

theorem edgeShift_mem_cubeSpan (K : Type) [Field K] (j : Fin 3) (M : Mat K)
    (hM : M ∈ cubeSpan K) : edgeShift K j M ∈ cubeSpan K := by
  induction hM using Submodule.span_induction with
  | mem N hN =>
    obtain ⟨a, rfl⟩ := hN
    rw [edgeShift_cube]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Function.update a j 1, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add N P _ _ hN hP => rw [map_add]; exact Submodule.add_mem _ hN hP
  | smul c N _ hN => rw [map_smul]; exact Submodule.smul_mem _ c hN

theorem outerLinear_on_cubeSpan (K : Type) [Field K] (j : Fin 3) (t : K) (M : Mat K)
    (hM : M ∈ cubeSpan K) : outerLinear K j t M = M + t • edgeShift K j M := by
  induction hM using Submodule.span_induction with
  | mem N hN =>
    obtain ⟨a, rfl⟩ := hN
    exact outerLinear_cube_via_edgeShift K a j t
  | zero => simp only [map_zero, smul_zero, add_zero]
  | add N P _ _ hN hP =>
    simp only [map_add, hN, hP, smul_add]
    abel
  | smul c N _ hN =>
    simp only [map_smul, hN, smul_add, smul_smul, mul_comm]

theorem edgeShift_commute (K : Type) [Field K] (i j : Fin 3) :
    Commute (edgeShift K i) (edgeShift K j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  have hroot : Commute (outerWord K i 1) (outerWord K j 1) :=
    CFSGTrialityGeckShortParameterWeyl.outer_roots_commute K i j hij false false 1 1
  have hlinear := hroot.map (CFSGAlgebraConjugationAction.action K (Mat K))
  change edgeShift K i * edgeShift K j = edgeShift K j * edgeShift K i
  apply LinearMap.ext
  intro M
  have hA := congrArg (fun L : Mat K ≃ₗ[K] Mat K => L M) hlinear.eq
  change outerLinear K i 1 (outerLinear K j 1 M) =
    outerLinear K j 1 (outerLinear K i 1 M) at hA
  change outerLinear K i 1 (outerLinear K j 1 M - M) - (outerLinear K j 1 M - M) =
    outerLinear K j 1 (outerLinear K i 1 M - M) - (outerLinear K i 1 M - M)
  rw [map_sub, map_sub, hA]
  abel

theorem span_tensorBasis_eq (K : Type) [Field K] :
    Submodule.span K (Set.range (tensorBasis K)) = cubeSpan K := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨ε, hε, he⟩ := tensorBasis_unit_sign a
    rw [he K]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨ε, hε, he⟩ := tensorBasis_unit_sign a
    have hsquare : (ε:K)*(ε:K)=1 := by rcases hε with rfl | rfl <;> norm_num
    have hmem := Submodule.smul_mem (Submodule.span K (Set.range (tensorBasis K))) (ε:K)
      (Submodule.subset_span (Set.mem_range_self a))
    rw [he K, smul_smul, hsquare, one_smul] at hmem
    exact hmem

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeSpanActions
