import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenHighRankTopModels
import SymmetricSubgroupAsymptotics.BinaryPairKernelNormalGenerators
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.PGroupCoinvariantGenerators

/-! An actual element with one cyclic orbit on the eight pair labels
forces every original normal subkernel to have one normal generator.
Thus a rank-five source with top rank at most three cannot have such an
element. The correlated kernel, actual lift offsets, and original top
are unchanged; no cyclic-group or degree-sixteen action census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction U (Fin 8)]
    (hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i)

include hact

theorem normalGen_le_one_of_single_cyclic_orbit (hU : IsPGroup 2 U) (g : U)
    (hcycle : Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (Fin 8)) = 1)
    (A : Subgroup U) [A.Normal] (hA : A ≤ F.top.ker) : MarkedC4.normalGen A ≤ 1 := by
  letI singleCyclicOrbitRankBound_factTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U (Fin 8)) 1 := by
    apply pGroup_uniformSubrepresentationGeneratorBound_of_head_le hU
    intro M
    exact (permutation_subrepresentationHead_le_cyclicOrbitCount
      (k := ZMod 2) (G := U) (X := Fin 8) M g).trans_eq hcycle
  exact F.normalGen_le_of_uniform_pair_module hact 1 hu A hA

theorem genRank_le_top_add_one_of_single_cyclic_orbit (hU : IsPGroup 2 U) (g : U)
    (hcycle : Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (Fin 8)) = 1) :
    MarkedC4.genRank U ≤ MarkedC4.genRank F.top.range + 1 := by
  have hk := F.normalGen_le_one_of_single_cyclic_orbit hact hU g hcycle F.top.ker le_rfl
  have hb := F.genRank_le_actual_pair_kernel_add_top
  omega

theorem no_single_cyclic_orbit_of_rank_five (hU : IsPGroup 2 U)
    (hrank : 5 ≤ MarkedC4.genRank U) (htop : MarkedC4.genRank F.top.range ≤ 3) :
    ¬ ∃ g : U, Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (Fin 8)) = 1 := by
  rintro ⟨g, hg⟩
  have hb := F.genRank_le_top_add_one_of_single_cyclic_orbit hact hU g hg
  omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
