import SymmetricSubgroupAsymptotics.BinaryPairCanonicalRadicalMembership

/-! The canonical carry state is exactly the whole original pair kernel,
expressed through the literal canonical layer matrix. This transports the
correlated subspace, not only its two projections or its dimension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

private theorem canonical_whole_axis_eq_kernelSpace :
    (F.axisNaturalSubrepresentation F.top.ker).toSubmodule = F.kernelSpace := by
  apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
  rintro v ⟨a,rfl⟩
  exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property

theorem canonical_kernelSpace_eq_comap
    (S : Submodule (ZMod 2) (Fin 16 → ZMod 2))
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule = S) :
    (F.reindex E.canonicalPointLabels).kernelSpace = S.comap binaryEightCanonicalLayerChange := by
  let e := E.canonicalPointLabels
  have hs : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap = S := by
    change (F.axisNaturalSubrepresentation F.top.ker).toSubmodule.map
      E.originalCoordinateEquiv.toLinearMap = S at hS
    rwa [F.canonical_whole_axis_eq_kernelSpace] at hS
  ext v
  constructor
  · rintro ⟨a,rfl⟩
    let k : F.top.ker := ⟨a.toMul.val,by
      have hk : a.toMul.val ∈ (F.reindex e).top.ker := a.toMul.property
      exact (congrArg (fun K : Subgroup U => a.toMul.val ∈ K) (F.reindex_top_ker e)).mp hk⟩
    have he : F.reindexKernel e k = a.toMul := Subtype.ext rfl
    have hb : (F.reindex e).bits a.toMul = fun j => F.bits k (e.symm j) := by
      funext j
      rw [← he,F.reindexKernel_bits]
    change binaryEightCanonicalLayerChange ((F.reindex e).bits a.toMul) ∈ S
    rw [hb,← E.originalCoordinateEquiv_canonicalPointLabels,← hs]
    exact ⟨F.bits k,⟨Additive.ofMul k,rfl⟩,rfl⟩
  · intro hv
    change binaryEightCanonicalLayerChange v ∈ S at hv
    rw [← hs] at hv
    obtain ⟨w,⟨a,rfl⟩,he⟩ := hv
    refine ⟨Additive.ofMul (F.reindexKernel e a.toMul),?_⟩
    change (F.reindex e).bits (F.reindexKernel e a.toMul) = v
    have hli : Function.Injective binaryEightCanonicalLayerChange := by
      rw [canonicalLayerChange_eq]
      exact binaryEightCanonicalPairFrame.originalCoordinateEquiv.injective
    apply hli
    have hb : (F.reindex e).bits (F.reindexKernel e a.toMul) =
        fun j => F.bits a.toMul (e.symm j) := by
      funext j
      exact F.reindexKernel_bits e a.toMul j
    rw [hb,← E.originalCoordinateEquiv_canonicalPointLabels]
    exact he

end SymmetricSubgroupAsymptotics.BinaryPairFrame
