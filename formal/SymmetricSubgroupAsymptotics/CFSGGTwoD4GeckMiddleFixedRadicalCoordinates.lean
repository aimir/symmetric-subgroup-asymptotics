import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedLift
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayerSurjective
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift

/-! The actual diagram-fixed middle radical has a four-coordinate
projection with exactly the highest-root kernel. Surjectivity uses a
genuine radical-word lift, then proves that same word fixed from its
actual highest-root defect in characteristic different from three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedRadicalCoordinates

open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleLayerCoordinates
open CFSGTrialityGeckMiddleCubeEquiv CFSGTrialityGeckMiddleFixedLayer
open CFSGTrialityGeckMatrixTwist CFSGGradedMatrixGroupFirstLayer
open CFSGGTwoD4GeckMiddleFixedLift CFSGGTwoD4GeckMiddleFixedCoordinates
open CFSGTrialityGeckMiddleFirstLayerSurjective CFSGCentralTwistedCommutatorLift
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def fixedMiddle (K : Type) [Field K] : Subgroup (Raw K) :=
  middleRadical K ⊓ fixedSubgroup (unitTwist K (RingEquiv.refl K))

private theorem exists_coordinate (K : Type) [Field K] [Finite K] (u : fixedMiddle K) :
    ∃ c : Fin 4 → K, (fixedCubeEmbedding K c).val = firstLayer middleWeight u.val := by
  let M : CFSGTrialityGeckMiddleCubeSpanActions.cubeSpan K :=
    ⟨firstLayer middleWeight u.val,firstLayer_mem_cubeSpan K ⟨u.val,u.property.1⟩⟩
  have hM : CFSGGTwoD4GeckMiddleDiagramAction.cubeDiagram K M = M := by
    apply Subtype.ext
    exact (matrixTwist_firstLayer K (RingEquiv.refl K) u.val).trans
      (congrArg (firstLayer middleWeight) u.property.2)
  obtain ⟨c,hc⟩ := exists_fixedCubeEmbedding K M hM
  exact ⟨c,congrArg Subtype.val hc⟩

def coordinate (K : Type) [Field K] [Finite K] (u : fixedMiddle K) : Fin 4 → K :=
  Classical.choose (exists_coordinate K u)

theorem coordinate_spec (K : Type) [Field K] [Finite K] (u : fixedMiddle K) :
    (fixedCubeEmbedding K (coordinate K u)).val = firstLayer middleWeight u.val :=
  Classical.choose_spec (exists_coordinate K u)

theorem coordinate_one (K : Type) [Field K] [Finite K] : coordinate K 1 = 0 := by
  apply fixedCubeEmbedding_injective K
  apply Subtype.ext
  have he0 : (fixedCubeEmbedding K 0).val = 0 := congrArg Subtype.val (map_zero (fixedCubeEmbedding K))
  exact (coordinate_spec K 1).trans ((firstLayer_one middleWeight).trans he0.symm)

theorem coordinate_mul (K : Type) [Field K] [Finite K] (u v : fixedMiddle K) :
    coordinate K (u*v) = coordinate K u + coordinate K v := by
  apply fixedCubeEmbedding_injective K
  rw [map_add]
  apply Subtype.ext
  change (fixedCubeEmbedding K (coordinate K (u*v))).val =
    (fixedCubeEmbedding K (coordinate K u)).val + (fixedCubeEmbedding K (coordinate K v)).val
  rw [coordinate_spec,coordinate_spec,coordinate_spec]
  exact firstLayer_mul middleWeight u.val v.val (middle_le_strict K u.property.1)
    (middle_le_strict K v.property.1)

def projection (K : Type) [Field K] [Finite K] : fixedMiddle K →* Multiplicative (Fin 4 → K) where
  toFun u := Multiplicative.ofAdd (coordinate K u)
  map_one' := congrArg Multiplicative.ofAdd (coordinate_one K)
  map_mul' u v := congrArg Multiplicative.ofAdd (coordinate_mul K u v)

theorem projection_surjective (K : Type) [Field K] [Finite K] (hthree : (3 : K) ≠ 0) :
    Function.Surjective (projection K) := by
  intro c
  obtain ⟨u,hu⟩ := firstLayer_lifts K (fixedCubeEmbedding K c.toAdd).val (fixedCubeEmbedding K c.toAdd).property
  have hfirst : matrixTwist K (RingEquiv.refl K) (firstLayer middleWeight u.val) =
      firstLayer middleWeight u.val :=
    (congrArg (matrixTwist K (RingEquiv.refl K)) hu).trans
      ((congrArg Subtype.val (fixedCubeEmbedding_fixed K c.toAdd)).trans hu.symm)
  have hfix := fixed_of_fixed_firstLayer K hthree u hfirst
  let v : fixedMiddle K := ⟨u.val,u.property,hfix⟩
  refine ⟨v,congrArg Multiplicative.ofAdd ?_⟩
  apply fixedCubeEmbedding_injective K
  apply Subtype.ext
  exact (coordinate_spec K v).trans hu

theorem mem_projection_kernel_iff (K : Type) [Field K] [Finite K] (u : fixedMiddle K) :
    u ∈ (projection K).ker ↔ u.val ∈ highestLine K := by
  let v : middleRadical K := ⟨u.val,u.property.1⟩
  constructor
  · intro hu
    have hc : coordinate K u = 0 := hu
    have he0 : (fixedCubeEmbedding K 0).val = 0 := congrArg Subtype.val (map_zero (fixedCubeEmbedding K))
    have hz : firstLayer middleWeight u.val = 0 :=
      (coordinate_spec K u).symm.trans
        ((congrArg (fun c : Fin 4 → K => (fixedCubeEmbedding K c).val) hc).trans he0)
    have hk : v ∈ (middleFirstLayerHom K).ker := hz
    rw [firstLayer_kernel_eq_highest] at hk
    exact hk
  · intro hu
    have hk : v ∈ (middleFirstLayerHom K).ker := by
      rw [firstLayer_kernel_eq_highest]
      exact hu
    have hz : firstLayer middleWeight u.val = 0 := hk
    change coordinate K u = 0
    apply fixedCubeEmbedding_injective K
    apply Subtype.ext
    have he0 : (fixedCubeEmbedding K 0).val = 0 := congrArg Subtype.val (map_zero (fixedCubeEmbedding K))
    exact (coordinate_spec K u).trans (hz.trans he0.symm)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
