import SymmetricSubgroupAsymptotics.BinaryDegreeSixteenJointWidthRankModels
import SymmetricSubgroupAsymptotics.BinaryPairRegularKernelSplit
import SymmetricSubgroupAsymptotics.BinaryPairHeisenbergKernelSplit
import SymmetricSubgroupAsymptotics.PGroupGeneratorAbelianizationOrder

/-! The joint rank/width frontier yields actual zero-offset permutation
models. Kernel-radical saturation is proved from the full original
abelianization order, not assumed as an additional structure input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]

include F in
private theorem abelianization_card_eq_sixty_four_of_rank_six
    (hU : IsPGroup 2 U) (hhigh : 6 ≤ MarkedC4.genRank U) :
    Nat.card (Abelianization U) = 64 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdegree : Nat.card X = 16 := by
    rw [← Nat.card_congr F.frame, Nat.card_prod, Nat.card_fin, Nat.card_zmod]
  have hu := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
  rw [hdegree] at hu
  norm_num at hu
  have hl := (Nat.pow_le_pow_right (by decide : 0 < 2) hhigh).trans
    (pGroup_pow_genRank_le_abelianization_card 2 hU)
  norm_num at hl
  omega

private theorem regular_kernel_saturated_of_rank_six
    (hU : IsPGroup 2 U) (hhigh : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)) :
    primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U := by
  have hab := F.abelianization_card_eq_sixty_four_of_rank_six hU hhigh
  have ht : Nat.card (Abelianization F.top.range) = 8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).abelianizationCongr.toEquiv).trans
      BinaryEightTopAbelianizationCards.regular_abelianization_card
  have hmax := F.regular_axis_normalGen_le hU F.top.ker le_rfl hH
  have hext := F.abelianization_card_le_actual_kernel_normalGen hU
  rw [hab, ht] at hext
  have hpow : 2 ^ 3 ≤ 2 ^ MarkedC4.normalGen F.top.ker := by nlinarith
  have hmin := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have heq : MarkedC4.normalGen F.top.ker = 3 := by omega
  apply F.saturated_pair_kernel_radical hU
  rw [hab,heq,ht]
  norm_num

private theorem heisenberg_kernel_saturated_of_rank_six
    (hU : IsPGroup 2 U) (hhigh : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)) :
    primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U := by
  have hab := F.abelianization_card_eq_sixty_four_of_rank_six hU hhigh
  have ht : Nat.card (Abelianization F.top.range) = 16 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).abelianizationCongr.toEquiv).trans
      BinaryEightTopAbelianizationCards.heisenberg_abelianization_card
  have hmax := F.heisenberg_axis_normalGen_le hU F.top.ker le_rfl hH
  have hext := F.abelianization_card_le_actual_kernel_normalGen hU
  rw [hab, ht] at hext
  have hpow : 2 ^ 2 ≤ 2 ^ MarkedC4.normalGen F.top.ker := by nlinarith
  have hmin := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have heq : MarkedC4.normalGen F.top.ker = 2 := by omega
  apply F.saturated_pair_kernel_radical hU
  rw [hab,heq,ht]
  norm_num

/-- In the first surviving template, the original extension is literally
point-conjugate to its same-kernel zero-offset model. -/
theorem regular46_joint_exists_zero_offset_model
    (hU : IsPGroup 2 U) (hhigh : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K46)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryRegularEightSquareCarry.R46) :
    ∃ (u : Fin 3 → U) (a : Fin 8 → ZMod 2),
      (∀ i, F.top (u i) = BinaryMenuCayley8T3.generators i) ∧
      U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom =
        F.affineGeneratedModel F.kernelSpace (fun i => F.top (u i)) (fun _ => 0) := by
  have hlift (i : Fin 3) : ∃ u : U, F.top u = BinaryMenuCayley8T3.generators i := by
    have hm : BinaryMenuCayley8T3.generators i ∈ F.top.range := by
      rw [hH]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    exact hm
  choose u hu using hlift
  have hp : ∀ i j, F.top (u i) j = BinaryRegularEightSquareCarry.generatorImages i j := by
    intro i j
    rw [hu]
    exact (BinaryRegularEightSquareCarry.generatorImages_eq_original i j).symm
  have hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range := by
    rw [show (fun i => F.top (u i)) = BinaryMenuCayley8T3.generators from funext hu, ← hH]
  have hrad := F.regular_kernel_saturated_of_rank_six hU hhigh hH
  have hderived (k : F.top.ker) (hk : (k : U) ∈ commutator U) :
      F.bits k ∈ BinaryRegularEightSquareCarry.R46 := by
    rw [← hR, F.bits_mem_ambientAxis, hrad]
    exact ⟨k.property, hk⟩
  obtain ⟨a, ha⟩ := F.regular46_exists_physical_conjugate_zero_offset_model u hp hgen hK hderived
  exact ⟨u, a, hu, ha⟩

/-- The second surviving template has the same full original-action
normalization, with its original four selected top generators. -/
theorem heisenberg14_joint_exists_zero_offset_model
    (hU : IsPGroup 2 U) (hhigh : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hK : F.kernelSpace = BinaryHeisenbergEightSquareCarry.K14)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = BinaryHeisenbergEightSquareCarry.R14) :
    ∃ (u : Fin 4 → U) (a : Fin 8 → ZMod 2),
      (∀ i, F.top (u i) = BinaryHeisenbergEightSquareCarry.originalSelected i) ∧
      U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom =
        F.affineGeneratedModel F.kernelSpace (fun i => F.top (u i)) (fun _ => 0) := by
  have hlift (i : Fin 4) : ∃ u : U,
      F.top u = BinaryHeisenbergEightSquareCarry.originalSelected i := by
    have hm : BinaryHeisenbergEightSquareCarry.originalSelected i ∈ F.top.range := by
      rw [hH]
      exact Subgroup.subset_closure ⟨⟨i.val + 1, by omega⟩, rfl⟩
    exact hm
  choose u hu using hlift
  have hgen : Subgroup.closure (Set.range fun i => F.top (u i)) = F.top.range := by
    rw [show (fun i => F.top (u i)) = BinaryHeisenbergEightSquareCarry.originalSelected from funext hu,
      BinaryHeisenbergEightSquareCarry.selected_closure_eq_original, ← hH]
  have hrad := F.heisenberg_kernel_saturated_of_rank_six hU hhigh hH
  have hderived (k : F.top.ker) (hk : (k : U) ∈ commutator U) :
      F.bits k ∈ BinaryHeisenbergEightSquareCarry.R14 := by
    rw [← hR, F.bits_mem_ambientAxis, hrad]
    exact ⟨k.property, hk⟩
  obtain ⟨a, ha⟩ := F.heisenberg14_exists_physical_conjugate_zero_offset_model
    u hu hgen hK hderived
  exact ⟨u, a, hu, ha⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
