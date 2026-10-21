import SymmetricSubgroupAsymptotics.BinaryPairSmallTopSectionUnit
import SymmetricSubgroupAsymptotics.BinaryPairSmallTopLargeKernel

/-! Actual rank-preserving normal-F unit packets at every nonelementary
transitive eight-pair top of order at most32. Full original abelianization
exponent two is a genuine consumer hypothesis, supplied by the general
proved excess-one exponent theorem. No E8 containment or top catalogue is
assumed;11 and21 are included. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction U (Fin 8)]
    [MulAction.IsPretransitive U (Fin 8)]
    [MulAction.IsPretransitive F.top.range (Fin 8)]
    (hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i)

include hact in
/-- The SAME original normal N and quotient U/N throughout. -/
theorem small_pair_top_rank_five_rank_preserving_unit
    (hU : IsPGroup 2 U)
    (hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 8))
    (htop : Nat.card F.top.range ≤ 32)
    (htoprank : MarkedC4.genRank F.top.range ≤ 3)
    (hrank : MarkedC4.genRank U = 5)
    (hexp : ∀ a : Abelianization U, a ^ 2 = 1)
    (N : Subgroup U) [N.Normal]
    (hQrank : MarkedC4.genRank (U ⧸ N) = 5)
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  letI smallPairTopRankFive_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := hU.to_quotient N
  have hTop := F.top_isPGroup hU
  have hTopExp := abelianization_exponent_of_surjective F.top.rangeRestrict
    F.top.rangeRestrict_surjective 2 hexp
  have hTopAb : Nat.card (Abelianization F.top.range) ≤ 8 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hTop hTopExp]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) htoprank
  have hQExp := abelianization_exponent_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) 2 hexp
  have hQAb : Nat.card (Abelianization (U ⧸ N)) = 32 := by
    rw [pGroup_abelianization_card_eq_pow_genRank 2 hQ hQExp, hQrank]
    decide
  have hK := F.kernel_finrank_le_seven_of_rank_five hU (by omega) htoprank
  have hdim := (F.normalSpace N).finrank_quotient_add_finrank
  by_cases hsmall : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) ≤ 6
  · exact F.small_top_section_le_six_unit hact N hU hnon htop hTopAb
      (by omega) hQAb.le hnonab hsmall
  · have hseven : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) = 7 := by omega
    have hN := F.normal_eq_bot_of_section_seven hU hK N hseven
    have hcenter : Nat.card (Subgroup.center (U ⧸ N)) ≤ 2 := by
      let e : U ⧸ N ≃* U :=
        (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
      rw [Nat.card_congr (RDTDegreeEightExceptionalTransport.centerEquiv e).toEquiv]
      exact F.original_center_le_two_of_large_kernel hU (by omega)
    have hcard : Nat.card (U ⧸ N) ≤ 4096 := by
      simpa using F.section_order_le_of_finrank_le N 7 32 (by omega) htop
    exact BinaryRankFiveCardUnitBounds.unit_of_card_le_fourThousand_center_le_two
      hQ (by omega) hcard hcenter

end SymmetricSubgroupAsymptotics.BinaryPairFrame
