import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleDiagramAction

/-! Four literal coordinates for the diagram-fixed D4 middle cube.
The two length-three coefficient orbits are retained in the actual
signed tensor basis. This is a linear fixed-space statement, not yet
an assertion that group fixed points lift from a quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedCoordinates

open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckMiddleLayerCoordinates CFSGTrialityGeckMatrixTwist
open CFSGGTwoD4GeckMiddleDiagramAction
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private def orbitSlot (i : Fin 8) : Fin 4 := match i.val with
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 1 | 5 => 2 | 6 => 2 | _ => 3

def orbitEmbedding (K : Type) [Field K] : (Fin 4 → K) →ₗ[K] (Fin 8 → K) where
  toFun c i := c (orbitSlot i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem orbitEmbedding_injective (K : Type) [Field K] : Function.Injective (orbitEmbedding K) := by
  intro c d he
  funext j
  fin_cases j
  · exact congrFun he 0
  · exact congrFun he 1
  · exact congrFun he 3
  · exact congrFun he 7

def fixedCubeEmbedding (K : Type) [Field K] : (Fin 4 → K) →ₗ[K] cubeSpan K :=
  ((tensorCoordinates K).comp (orbitEmbedding K)).codRestrict (cubeSpan K) (fun c =>
    (tensorCoordinates_range K).le ⟨orbitEmbedding K c,rfl⟩)

theorem fixedCubeEmbedding_injective (K : Type) [Field K] : Function.Injective (fixedCubeEmbedding K) := by
  intro c d he
  exact orbitEmbedding_injective K (tensorCoordinates_injective K (congrArg Subtype.val he))

theorem fixedCubeEmbedding_fixed (K : Type) [Field K] (c : Fin 4 → K) :
    cubeDiagram K (fixedCubeEmbedding K c) = fixedCubeEmbedding K c := by
  have hs : ∀ i : Fin 8, orbitSlot (tensorCycle i) = orbitSlot i := by
    intro i
    fin_cases i <;> rfl
  apply Subtype.ext
  have ht := matrixTwist_tensorCoordinates K (RingEquiv.refl K) (orbitEmbedding K c)
  change matrixTwist K (RingEquiv.refl K) (tensorCoordinates K (orbitEmbedding K c)) = _
  refine ht.trans (congrArg (tensorCoordinates K) ?_)
  funext i
  change c (orbitSlot (tensorCycle.symm i)) = c (orbitSlot i)
  exact congrArg c (by simpa only [Equiv.apply_symm_apply] using (hs (tensorCycle.symm i)).symm)

theorem exists_fixedCubeEmbedding (K : Type) [Field K] (M : cubeSpan K)
    (hM : cubeDiagram K M = M) : ∃ c : Fin 4 → K, fixedCubeEmbedding K c = M := by
  have hm : M.val ∈ (tensorCoordinates K).range := (tensorCoordinates_range K).ge M.property
  obtain ⟨d,hd⟩ := hm
  have hf : matrixTwist K (RingEquiv.refl K) (tensorCoordinates K d) = tensorCoordinates K d :=
    (congrArg (matrixTwist K (RingEquiv.refl K)) hd).trans
      ((congrArg Subtype.val hM).trans hd.symm)
  obtain ⟨_,_,h2,h4,h6,h5⟩ := fixed_tensorCoordinate_conditions K (RingEquiv.refl K) d hf
  let c : Fin 4 → K := fun j => match j.val with
    | 0 => d 0 | 1 => d 1 | 2 => d 3 | _ => d 7
  have hc : orbitEmbedding K c = d := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact h2.symm
    · rfl
    · exact h2.symm.trans h4.symm
    · exact h6.symm.trans h5.symm
    · exact h6.symm
    · rfl
  refine ⟨c,Subtype.ext ?_⟩
  change tensorCoordinates K (orbitEmbedding K c) = M.val
  exact (congrArg (tensorCoordinates K) hc).trans hd

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedCoordinates
