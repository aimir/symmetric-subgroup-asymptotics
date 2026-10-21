import SymmetricSubgroupAsymptotics.BinaryHeisenbergRankSixCards
import SymmetricSubgroupAsymptotics.BinaryPairKernelRadicalDerived

/-! The original rank-five source has one extra bit of derived capacity.
Its same actual kernel and top orders fix the source size independently of
any splitting or equality between the radical and derived intersection. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem heisenberg_rank_five_card_bounds
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (r : ℕ) (hK : Nat.card F.kernelSpace = 4 * r) :
    Nat.card U = 128 * r ∧ Nat.card (commutator U) ≤ 4 * r := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht : Nat.card F.top.range = 32 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans
      BinaryMenuCayley8T22.exact_card
  have hc := F.kernelSpace_card_mul_top
  rw [hK, ht] at hc
  have hu : Nat.card U = 128 * r := by nlinarith
  have ha : 32 ≤ Nat.card (Abelianization U) :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
  have hd := (commutator U).card_eq_card_quotient_mul_card_subgroup
  change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hd
  rw [hu] at hd
  exact ⟨hu, by nlinarith⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
