import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerProducts
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantExactDenominator

/-! The pair-layer head filtration retains the actual kernel product
inside the original point-module radical. The lower layer is charged
only after dividing by that product and its own intrinsic radical. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))
  (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))

def pairConstantLayerInclusion :
    (F.pairConstantModuleLayer W).toRepresentation.IntertwiningMap W.toRepresentation where
  toLinearMap := (F.pairConstant.comp (F.pairConstantModuleLayer W).toSubmodule.subtype).codRestrict
    W.toSubmodule (fun v => v.property)
  isIntertwining' u := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ F.pairConstantIntertwiner u v.val

def pairSumLayerProjection :
    W.toRepresentation.IntertwiningMap (F.pairSumModuleLayer W).toRepresentation where
  toLinearMap := (F.pairSum.comp W.toSubmodule.subtype).codRestrict
    (F.pairSumModuleLayer W).toSubmodule (fun v => ⟨v.val, v.property, rfl⟩)
  isIntertwining' u := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ F.pairSumIntertwiner u v.val

theorem pairSumLayerProjection_surjective : Function.Surjective (F.pairSumLayerProjection W) := by
  rintro ⟨x, v, hv, rfl⟩
  exact ⟨⟨v, hv⟩, rfl⟩

theorem pairModuleLayers_exact :
    (F.pairConstantLayerInclusion W).toLinearMap.range =
      (F.pairSumLayerProjection W).toLinearMap.ker := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change F.pairSum (F.pairConstant a.val) = 0
    exact F.pairSum_pairConstant a.val
  · intro v hv
    have hv0 : F.pairSum v.val = 0 := congrArg Subtype.val hv
    have hvker : v.val ∈ F.pairSumIntertwiner.toLinearMap.ker := hv0
    obtain ⟨a, ha⟩ := F.pairConstant_pairSum_exact_linear.ge hvker
    change F.pairConstant a = v.val at ha
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    change F.pairConstant a ∈ W.toSubmodule
    rw [ha]
    exact v.property

def pairLayerProductDenominator : Submodule (ZMod 2) (F.pairConstantModuleLayer W).toSubmodule :=
  (binaryCoordinateProductSpan F.kernelSpace (F.pairSumModuleLayer W).toSubmodule).comap
      (F.pairConstantModuleLayer W).toSubmodule.subtype ⊔
    Representation.Coinvariants.ker (F.pairConstantModuleLayer W).toRepresentation

/-- Both terms of the actual lower denominator vanish in the original
point-module head. No invariant forms are assumed to extend. -/
theorem pairLayerProductDenominator_le_head_kernel :
    F.pairLayerProductDenominator W ≤
      ((Representation.Coinvariants.mk W.toRepresentation).comp
        (F.pairConstantLayerInclusion W).toLinearMap).ker := by
  apply sup_le
  · intro v hv
    apply LinearMap.mem_ker.mpr
    change Representation.Coinvariants.mk W.toRepresentation
      (F.pairConstantLayerInclusion W v) = 0
    have hm := F.actual_kernel_pairSum_product_map_le_point_radical W
      (show F.pairConstant v.val ∈
        (binaryCoordinateProductSpan F.kernelSpace (F.pairSumModuleLayer W).toSubmodule).map
          F.pairConstant from ⟨v.val, hv, rfl⟩)
    obtain ⟨a, ha, he⟩ := hm
    have heq : a = F.pairConstantLayerInclusion W v := Subtype.ext he
    exact (Representation.Coinvariants.mk_eq_zero W.toRepresentation).mpr (heq ▸ ha)
  · intro v hv
    apply LinearMap.mem_ker.mpr
    change Representation.Coinvariants.mk W.toRepresentation
      (F.pairConstantLayerInclusion W v) = 0
    have hz := (Representation.Coinvariants.mk_eq_zero
      (F.pairConstantModuleLayer W).toRepresentation).mpr hv
    rw [← Representation.Coinvariants.map_mk (F.pairConstantLayerInclusion W) v, hz, map_zero]

/-- Exact two-layer head bound with the original cross-layer denominator. -/
theorem pairModuleHead_le_product_quotient_add [Finite X] :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤
      Module.finrank (ZMod 2)
        ((F.pairConstantModuleLayer W).toSubmodule ⧸ F.pairLayerProductDenominator W) +
      Module.finrank (ZMod 2) (F.pairSumModuleLayer W).toRepresentation.Coinvariants :=
  RepresentationCoinvariantExactDenominator.finrank_coinvariants_le_quotient_add
    (F.pairConstantLayerInclusion W) (F.pairSumLayerProjection W)
    (F.pairSumLayerProjection_surjective W) (F.pairModuleLayers_exact W)
    (F.pairLayerProductDenominator W) (F.pairLayerProductDenominator_le_head_kernel W)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
