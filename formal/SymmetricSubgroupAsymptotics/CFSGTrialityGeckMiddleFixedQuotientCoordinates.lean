import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedTensorImage
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleLayerCoordinates

/-! Coordinates of the literal fixed middle radical. Existence uses actual
fixed words and surjectivity uses the constructed fixed lifts. The kernel
is the actual highest root line; no fixed-quotient lifting is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedQuotientCoordinates

open CFSGTrialityGeckDiagramCovariance
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityGeckMiddleFixedTensorImage
open CFSGTrialityGeckMiddleLayerCoordinates CFSGTrialityGeckMiddleFixedLiftSpan
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleCubeEquiv
open CFSGTrialityGeckFixedPositiveRaw CFSGGradedMatrixGroupFirstLayer

local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private theorem exists_coordinate (q : CFSG.PrimePower) (u : fixedMiddle q) :
    ∃ c : fullEnvelope q, fixedTensorEmbedding q c = firstLayer middleWeight u.val := by
  have hu := ((mem_fixedPositiveRaw_iff q u.val).mp u.property.2).2
  obtain ⟨c, hc, he⟩ := exists_fixed_firstLayer_coordinates q ⟨u.val,u.property.1⟩ hu
  exact ⟨⟨c,hc⟩,he⟩

def coordinate (q : CFSG.PrimePower) (u : fixedMiddle q) : fullEnvelope q :=
  Classical.choose (exists_coordinate q u)

theorem coordinate_spec (q : CFSG.PrimePower) (u : fixedMiddle q) :
    fixedTensorEmbedding q (coordinate q u) = firstLayer middleWeight u.val :=
  Classical.choose_spec (exists_coordinate q u)

theorem coordinate_one (q : CFSG.PrimePower) : coordinate q 1 = 0 := by
  apply fixedTensorEmbedding_injective q
  rw [coordinate_spec,map_zero]
  exact firstLayer_one middleWeight

theorem coordinate_mul (q : CFSG.PrimePower) (u v : fixedMiddle q) :
    coordinate q (u*v) = coordinate q u + coordinate q v := by
  apply fixedTensorEmbedding_injective q
  rw [coordinate_spec,map_add,coordinate_spec,coordinate_spec]
  exact firstLayer_mul middleWeight u.val v.val
    (middle_le_strict _ u.property.1) (middle_le_strict _ v.property.1)

def projection (q : CFSG.PrimePower) : fixedMiddle q →* Multiplicative (fullEnvelope q) where
  toFun u := Multiplicative.ofAdd (coordinate q u)
  map_one' := congrArg Multiplicative.ofAdd (coordinate_one q)
  map_mul' u v := congrArg Multiplicative.ofAdd (coordinate_mul q u v)

theorem projection_surjective (q : CFSG.PrimePower) : Function.Surjective (projection q) := by
  intro c
  obtain ⟨u,hu⟩ := fixed_fullEnvelope_lifts q c.toAdd.val c.toAdd.property
  refine ⟨u,congrArg Multiplicative.ofAdd ?_⟩
  apply fixedTensorEmbedding_injective q
  exact (coordinate_spec q u).trans hu

theorem mem_projection_kernel_iff (q : CFSG.PrimePower) (u : fixedMiddle q) :
    u ∈ (projection q).ker ↔ u.val ∈ highestLine (K q) := by
  have he : coordinate q u = 0 ↔ firstLayer middleWeight u.val = 0 := by
    constructor
    · intro hz
      exact (coordinate_spec q u).symm.trans ((congrArg (fixedTensorEmbedding q) hz).trans (map_zero _))
    · intro hz
      apply fixedTensorEmbedding_injective q
      exact (coordinate_spec q u).trans (hz.trans (map_zero _).symm)
  change coordinate q u = 0 ↔ _
  rw [he]
  let v : middleRadical (K q) := ⟨u.val,u.property.1⟩
  have hk : v ∈ (middleFirstLayerHom (K q)).ker ↔ v ∈ highestInMiddle (K q) := by
    rw [firstLayer_kernel_eq_highest]
  exact hk

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedQuotientCoordinates
