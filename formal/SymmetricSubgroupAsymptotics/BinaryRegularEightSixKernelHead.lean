import SymmetricSubgroupAsymptotics.BinaryRegularEightSixKernelConjugacy
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel24
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.BinaryPairLiteralTopModel

/-! One selected chart24 pair-layer certificate handles every actual
six-dimensional regular-eight kernel after an explicit normalizer
reindexing. The original group, points, module, and all lift offsets stay
unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {U : Subgroup (Equiv.Perm X)} (E : BinaryPairFrame U (Fin 8))

theorem reindex_kernelSpace_map (p : Equiv.Perm (Fin 8)) :
    (E.reindex p).kernelSpace = E.kernelSpace.map
      (BinaryRegularEightSixKernelConjugacy.reindex p).toLinearMap := by
  apply le_antisymm
  · rintro v ⟨a, rfl⟩
    let k : E.top.ker := ⟨a.toMul.val, by
      simpa only [E.reindex_top_ker p] using a.toMul.property⟩
    have he : E.reindexKernel p k = a.toMul := Subtype.ext rfl
    refine ⟨E.bits k, ⟨Additive.ofMul k, rfl⟩, ?_⟩
    funext x
    change E.bits k (p.symm x) = (E.reindex p).bits a.toMul x
    rw [← E.reindexKernel_bits p k x, he]
  · rintro v ⟨z, ⟨a, rfl⟩, rfl⟩
    refine ⟨Additive.ofMul (E.reindexKernel p a.toMul), ?_⟩
    funext x
    exact E.reindexKernel_bits p a.toMul x

variable [Finite X]

theorem naturalModuleHead_le_three_of_regular_kernel_dimension_six
    (hH : E.top.range = BinaryRegularEightNaturalRegistry.H)
    (hdim : Module.finrank (ZMod 2) E.kernelSpace = 6)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 3 := by
  let K := E.literalTopAxis BinaryRegularEightNaturalRegistry.H hH E.top.ker
  have hKS : K.toSubmodule = E.kernelSpace := by
    change (E.literalTopAxis BinaryRegularEightNaturalRegistry.H hH E.top.ker).toSubmodule = E.kernelSpace
    rw [E.literalTopAxis_space BinaryRegularEightNaturalRegistry.H hH E.top.ker]
    apply le_antisymm (E.ambientAxis_le_kernelSpace E.top.ker)
    rintro v ⟨a, rfl⟩
    exact (E.bits_mem_ambientAxis E.top.ker a.toMul).mpr a.toMul.property
  have hkdim : Module.finrank (ZMod 2) K.toSubmodule = 6 := by rw [hKS]; exact hdim
  obtain ⟨c, hc⟩ := BinaryRegularEightSixKernelConjugacy.six_dimensional_state_conjugate K hkdim
  rw [hKS] at hc
  let p := BinaryRegularEightSixKernelConjugacy.conjugator c
  have hnewH : (E.reindex p).top.range = BinaryRegularEightNaturalRegistry.H := by
    rw [E.reindex_top_range_conjugation, hH]
    exact BinaryRegularEightSixKernelConjugacy.conjugator_normalizes c
  have hnewK : (E.reindex p).kernelSpace = BinaryRegularEightNaturalRegistry.chart24.space :=
    (E.reindex_kernelSpace_map p).trans hc
  exact (E.reindex p).naturalModuleHead_le_of_literal_pair_layer_bound
    BinaryRegularEightNaturalRegistry.H hnewH _ hnewK 3
    BinaryPairLayerHead8T3Kernel24.pair_bound W

end SymmetricSubgroupAsymptotics.BinaryPairFrame
