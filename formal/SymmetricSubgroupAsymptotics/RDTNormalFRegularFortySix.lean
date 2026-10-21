import SymmetricSubgroupAsymptotics.SmallDerivedNormalFBounds
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryHeads

/-! Every original regular-eight K46 extension has order128. Rank-six
saturation therefore puts its derived group below order two, and the
same normal-F packet handles all its nonabelian normal quotients. No
choice of split lifts or separate normal-subgroup certificate is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem regular46_original_card
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K46) :
    Nat.card U = 128 := by
  have hchart : F.kernelSpace =
      (BinaryRegularEightNaturalRegistry.charts 46).2.space :=
    (hK.trans BinaryRegularEightNaturalRegistry.kernel46_space.symm).trans
      (BinaryRegularEightNaturalRegistry.states_space 46)
  have hk : Nat.card F.kernelSpace = 16 := by
    rw [hchart, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      (BinaryRegularEightNaturalRegistry.charts 46).2.finrank]
    decide +kernel
  have ht : Nat.card F.top.range = 8 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans
      BinaryMenuCayley8T3.exact_card
  have h := F.kernelSpace_card_mul_top
  rw [hk, ht] at h
  exact h.symm

theorem regular46_five_quarters_normalF_packet
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hrank : 6 ≤ MarkedC4.genRank U)
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : F.kernelSpace = BinaryRegularEightSquareCarry.K46)
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ V : Subgroup (U ⧸ N), V.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog V +
        (5 / 4 : ℝ) * MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog V ≤ 4 := by
  have hdegree : Nat.card X = 16 := by
    rw [← Nat.card_congr F.frame, Nat.card_prod, Nat.card_fin, Nat.card_zmod]
  exact SmallDerivedNormalFBounds.sixteen_rank_six_small_order_packet hU hdegree
    (le_of_eq (F.regular46_original_card hH hK)) hrank N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
