import SymmetricSubgroupAsymptotics.BinaryPairPermutationGeneratorExtension
import SymmetricSubgroupAsymptotics.BinaryCoupledHeadCertificate
import Mathlib.RepresentationTheory.Coinvariants

/-! Literal pair-sum and pair-constant layers of an arbitrary natural
module state. The actual correlated pair kernel multiplies the upper
layer into the lower layer, and those products are killed in the head of
the original state by actual kernel displacements. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))
  (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))

def pairSumModuleLayer : Subrepresentation F.pulledBackCoordinateTopAction where
  toSubmodule := W.toSubmodule.map F.pairSum
  apply_mem_toSubmodule u := by
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨permutationFunctionRepresentation (ZMod 2) U X u f,
      W.apply_mem_toSubmodule u hf, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ F.pairSumIntertwiner u f

def pairConstantModuleLayer : Subrepresentation F.pulledBackCoordinateTopAction where
  toSubmodule := W.toSubmodule.comap F.pairConstant
  apply_mem_toSubmodule u v hv := by
    change F.pairConstant (F.pulledBackCoordinateTopAction u v) ∈ W.toSubmodule
    have he : F.pairConstant (F.pulledBackCoordinateTopAction u v) =
        permutationFunctionRepresentation (ZMod 2) U X u (F.pairConstant v) :=
      Representation.IntertwiningMap.isIntertwining _ _ F.pairConstantIntertwiner u v
    rw [he]
    exact W.apply_mem_toSubmodule u hv

/-- The product uses the actual kernel K, rather than the full flip space. -/
theorem actual_kernel_pairSum_product_le_constantLayer :
    binaryCoordinateProductSpan F.kernelSpace (F.pairSumModuleLayer W).toSubmodule ≤
      (F.pairConstantModuleLayer W).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨f, hf, rfl⟩ := hb
  change F.pairConstant (F.bits k.toMul * F.pairSum f) ∈ W.toSubmodule
  have he : permutationFunctionRepresentation (ZMod 2) U X k.toMul.val f - f =
      F.pairConstant (F.bits k.toMul * F.pairSum f) :=
    F.kernel_displacement_eq_pairConstant_product k.toMul f
  rw [← he]
  exact W.toSubmodule.sub_mem (W.apply_mem_toSubmodule k.toMul.val hf) hf

/-- Each cross-layer product is the coordinate of an actual displacement
in W. Thus its constant image lies in W's intrinsic coinvariant radical. -/
theorem actual_kernel_pairSum_product_map_le_point_radical :
    (binaryCoordinateProductSpan F.kernelSpace (F.pairSumModuleLayer W).toSubmodule).map
        F.pairConstant ≤
      (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨f, hf, rfl⟩ := hb
  change F.pairConstant (F.bits k.toMul * F.pairSum f) ∈
    (Representation.Coinvariants.ker W.toRepresentation).map W.toSubmodule.subtype
  refine ⟨W.toRepresentation k.toMul.val (⟨f, hf⟩ : W.toSubmodule) - ⟨f, hf⟩,
    Representation.Coinvariants.sub_mem_ker k.toMul.val (⟨f, hf⟩ : W.toSubmodule), ?_⟩
  change permutationFunctionRepresentation (ZMod 2) U X k.toMul.val f - f =
    F.pairConstant (F.bits k.toMul * F.pairSum f)
  exact F.kernel_displacement_eq_pairConstant_product k.toMul f

end SymmetricSubgroupAsymptotics.BinaryPairFrame
