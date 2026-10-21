import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenHighRankTopModels
import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerModelBound
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel45
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel12
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T22Kernel13

/-! Simultaneous rank-six and natural-width-four saturation leaves two
actual kernel templates. This is a statement about the original group
and its literal point module, with arbitrary original affine lifts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8))

theorem six_le_rank_four_le_head_literal_kernel_models
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hhigh : 6 ≤ MarkedC4.genRank U)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hwide : 4 ≤ Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) :
    (∃ g : Equiv.Perm (Fin 8),
      (F.reindex g).top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators) ∧
      (F.reindex g).kernelSpace = BinaryRegularEightSquareCarry.K46 ∧
      (F.reindex g).ambientAxis (primeRelativeRadical 2 (F.reindex g).top.ker) =
        BinaryRegularEightSquareCarry.R46) ∨
    (∃ g : Equiv.Perm (Fin 8),
      (F.reindex g).top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators) ∧
      (F.reindex g).kernelSpace = BinaryHeisenbergEightSquareCarry.K14 ∧
      (F.reindex g).ambientAxis (primeRelativeRadical 2 (F.reindex g).top.ker) =
        BinaryHeisenbergEightSquareCarry.R14) := by
  rcases F.six_le_genRank_literal_top_models hU hhigh with
    ⟨g, hH, hlarge⟩ | ⟨g, hH, hlarge⟩
  · let E := F.reindex g
    change 3 ≤ MarkedC4.normalGen E.top.ker at hlarge
    rcases E.regular_large_axis_models hU E.top.ker le_rfl hH (by omega) with
      ⟨hK, hR⟩ | ⟨hK, hR⟩
    · have hchart : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 45).2.space := by
        have he := E.ambientAxis_kernel.symm.trans hK
        rw [← BinaryRegularEightNaturalRegistry.kernel45_space,
          BinaryRegularEightNaturalRegistry.states_space] at he
        exact he
      have hb := E.naturalModuleHead_le_of_literal_pair_layer_bound
        BinaryRegularEightNaturalRegistry.H hH
        (BinaryRegularEightNaturalRegistry.charts 45).2.space hchart 3
        BinaryPairLayerHead8T3Kernel45.pair_bound W
      omega
    · exact Or.inl ⟨g, hH, E.ambientAxis_kernel.symm.trans hK, hR⟩
  · let E := F.reindex g
    change 2 ≤ MarkedC4.normalGen E.top.ker at hlarge
    rcases E.heisenberg_large_axis_models hU E.top.ker le_rfl hH (by omega) with
      ⟨hK, hR⟩ | ⟨hK, hR⟩ | ⟨hK, hR⟩
    · have hchart : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 12).2.space := by
        have he := E.ambientAxis_kernel.symm.trans hK
        rw [← BinaryHeisenbergEightNaturalHeads.kernel12_space,
          BinaryHeisenbergEightNaturalHeads.states_space] at he
        exact he
      have hb := E.naturalModuleHead_le_of_literal_pair_layer_bound
        BinaryHeisenbergEightNaturalHeads.H hH
        (BinaryHeisenbergEightNaturalHeads.charts 12).2.space hchart 2
        BinaryPairLayerHead8T22Kernel12.pair_bound W
      omega
    · have hchart : E.kernelSpace = (BinaryHeisenbergEightNaturalHeads.charts 13).2.space := by
        have he := E.ambientAxis_kernel.symm.trans hK
        rw [← BinaryHeisenbergEightNaturalHeads.kernel13_space,
          BinaryHeisenbergEightNaturalHeads.states_space] at he
        exact he
      have hb := E.naturalModuleHead_le_of_literal_pair_layer_bound
        BinaryHeisenbergEightNaturalHeads.H hH
        (BinaryHeisenbergEightNaturalHeads.charts 13).2.space hchart 3
        BinaryPairLayerHead8T22Kernel13.pair_bound W
      omega
    · exact Or.inr ⟨g, hH, E.ambientAxis_kernel.symm.trans hK, hR⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
