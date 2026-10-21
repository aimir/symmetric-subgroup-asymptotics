import SymmetricSubgroupAsymptotics.BinaryHeisenbergRankSixRadical
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard

/-! The exact original source and derived orders follow from the original
rank-six abelianization and top order. The correlated kernel is retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction.IsPretransitive U X]
include F

theorem heisenberg_rank_six_abelianization_card
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U) :
    Nat.card (Abelianization U) = 64 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdegree : Nat.card X = 16 := by
    rw [← Nat.card_congr F.frame, Nat.card_prod, Nat.card_fin, Nat.card_zmod]
  have habhi := twoGroup_transitive_abelianization_card_le_quarter_add_two U hU
  rw [hdegree] at habhi
  have hablo : 64 ≤ Nat.card (Abelianization U) :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
  norm_num at habhi
  omega

theorem heisenberg_rank_six_card_data
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (r : ℕ) (hK : Nat.card F.kernelSpace = 4 * r) :
    Nat.card U = 128 * r ∧ Nat.card (commutator U) = 2 * r := by
  have ht : Nat.card F.top.range = 32 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans
      BinaryMenuCayley8T22.exact_card
  have hc := F.kernelSpace_card_mul_top
  rw [hK, ht] at hc
  have hu : Nat.card U = 128 * r := by nlinarith
  have hd := (commutator U).card_eq_card_quotient_mul_card_subgroup
  change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hd
  rw [F.heisenberg_rank_six_abelianization_card hU hrank, hu] at hd
  exact ⟨hu, by omega⟩

theorem heisenberg_rank_six_radical_coordinate_le_derived
    (hU : IsPGroup 2 U) (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (R : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = R) :
    F.coordinateSubgroup R ≤ commutator U := by
  rw [← hR, F.coordinateSubgroup_ambientAxis,
    F.heisenberg_rank_six_kernel_radical_eq hU hrank hH]
  exact inf_le_right.trans inf_le_right

end SymmetricSubgroupAsymptotics.BinaryPairFrame
