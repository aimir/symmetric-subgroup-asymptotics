import SymmetricSubgroupAsymptotics.BinaryPairHighLayerDistinctness
import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenHighRankTopModels

/-! Every actual rank-five degree-sixteen pair source has a nonzero
original flip kernel, and hence contains the literal constant flip. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (E : BinaryPairFrame U (Fin 8))

theorem rank_five_kernelSpace_positive_finrank (hU : IsPGroup 2 U)
    (hrank : 5 ≤ MarkedC4.genRank U) :
    1 ≤ Module.finrank (ZMod 2) E.kernelSpace := by
  letI rankFiveKernelConstant_topTransitive : MulAction.IsPretransitive E.top.range (Fin 8) :=
    E.top_pretransitive
  have hp := E.top_isPGroup hU
  letI rankFiveKernelConstant_topNilpotent : Group.IsNilpotent E.top.range := hp.isNilpotent
  have hb := twoGroup_transitive_normalGen_le_quarter_add_two E.top.range hp
    (⊤ : Subgroup E.top.range)
  norm_num only [Nat.card_fin] at hb
  have ht : MarkedC4.genRank E.top.range ≤ 4 :=
    (MarkedC4.genRank_le_normalGen_top (G := E.top.range)).trans hb
  have hg := E.genRank_le_actual_pair_kernel_add_top
  have hk : 1 ≤ MarkedC4.normalGen E.top.ker := by omega
  let A := E.axisNaturalSubrepresentation E.top.ker
  have ha : A.toSubmodule = E.kernelSpace := by
    apply le_antisymm (E.ambientAxis_le_kernelSpace E.top.ker)
    rintro v ⟨a, rfl⟩
    exact (E.bits_mem_ambientAxis E.top.ker a.toMul).mpr a.toMul.property
  have hh : 1 ≤ Module.finrank (ZMod 2) A.toRepresentation.Coinvariants := by
    rw [← E.axisNatural_normalGen E.top.ker le_rfl hU]
    exact hk
  have hq := LinearMap.finrank_le_finrank_of_surjective
    (Representation.Coinvariants.mk_surjective A.toRepresentation)
  change Module.finrank (ZMod 2) A.toRepresentation.Coinvariants ≤
    Module.finrank (ZMod 2) A.toSubmodule at hq
  have hf : 1 ≤ Module.finrank (ZMod 2) A.toSubmodule := hh.trans hq
  have hd := congrArg
    (fun P : Submodule (ZMod 2) (Fin 8 → ZMod 2) => Module.finrank (ZMod 2) P) ha
  exact hf.trans_eq hd

theorem rank_five_kernelSpace_contains_one (hU : IsPGroup 2 U)
    (hrank : 5 ≤ MarkedC4.genRank U) : (1 : Fin 8 → ZMod 2) ∈ E.kernelSpace :=
  E.kernelSpace_contains_one_of_positive_finrank hU 0
    (E.rank_five_kernelSpace_positive_finrank hU hrank)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
