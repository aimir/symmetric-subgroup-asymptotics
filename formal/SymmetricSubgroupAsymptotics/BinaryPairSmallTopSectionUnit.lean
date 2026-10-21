import SymmetricSubgroupAsymptotics.BinaryPairSmallTopSectionOrders
import SymmetricSubgroupAsymptotics.OriginalKernelCenterProductBound
import SymmetricSubgroupAsymptotics.BinaryRankFiveCardUnitBounds
import SymmetricSubgroupAsymptotics.BinarySmallTopCenterBounds

/-! All original sections of dimension at most6 under an actual top of
order at most32. Small sections use actual quotient-centre incidence;
large sections use the checked nonelementary faithfulness theorem.
Every normal N and its original top image remain unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8)) [MulAction U (Fin 8)]
    [MulAction.IsPretransitive U (Fin 8)]
    [MulAction.IsPretransitive F.top.range (Fin 8)]
    (hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i)
    (N : Subgroup U) [N.Normal]

include hact in
/-- This is a local actual-quotient installer; the abelianization bounds
are supplied from the original excess-one exponent theorem in its caller. -/
theorem small_top_section_le_six_unit
    (hU : IsPGroup 2 U)
    (hnon : ¬ BinarySquareActionStructure.SquaresActTrivially (G := U) (X := Fin 8))
    (htop : Nat.card F.top.range ≤ 32)
    (hTopAb : Nat.card (Abelianization F.top.range) ≤ 8)
    (hQrank : 5 ≤ MarkedC4.genRank (U ⧸ N))
    (hQAb : Nat.card (Abelianization (U ⧸ N)) ≤ 32)
    (hnonab : ¬ ∀ a b : U ⧸ N, a*b=b*a)
    (hsection : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) ≤ 6) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  let B := U ⧸ (F.top.ker ⊔ N)
  have hB : IsPGroup 2 B := hU.to_quotient _
  have hQ : IsPGroup 2 (U ⧸ N) := hU.to_quotient N
  have hBcard : Nat.card B ≤ 32 :=
    (Nat.card_le_card_of_surjective (F.sectionTopQuotient N)
      (F.sectionTopQuotient_surjective N)).trans htop
  have hBAb : Nat.card (Abelianization B) ≤ 8 :=
    (F.section_base_abelianization_card_le N).trans hTopAb
  by_cases hsmall : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) ≤ 4
  · have hQcard : Nat.card (U ⧸ N) ≤ 512 := by
      simpa using F.section_order_le_of_finrank_le N 4 32 hsmall htop
    have hcenter : Nat.card (Subgroup.center (U ⧸ N)) ≤ 16 := by
      by_cases hBab : ∀ a b : B, a*b=b*a
      · letI smallTopSectionUnit_baseComm : IsMulCommutative B := ⟨⟨hBab⟩⟩
        have hb8 : Nat.card B ≤ 8 := by
          change Nat.card (B ⧸ commutator B) ≤ 8 at hBAb
          rw [commutator_eq_bot B] at hBAb
          rw [Nat.card_congr (QuotientGroup.quotientBot : (B ⧸ (⊥ : Subgroup B)) ≃* B).toEquiv] at hBAb
          exact hBAb
        have hq128 : Nat.card (U ⧸ N) ≤ 128 := by
          rw [F.section_order_eq N]
          exact (Nat.mul_le_mul
            (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hsmall) hb8)
        letI smallTopSectionUnit_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have ha : 32 ≤ Nat.card (Abelianization (U ⧸ N)) :=
          (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hQrank).trans
            (pGroup_pow_genRank_le_abelianization_card 2 hQ)
        have hc := (commutator (U ⧸ N)).card_eq_card_quotient_mul_card_subgroup
        change Nat.card (U ⧸ N) = Nat.card (Abelianization (U ⧸ N)) *
          Nat.card (commutator (U ⧸ N)) at hc
        have hd : Nat.card (commutator (U ⧸ N)) ≤ 4 := by nlinarith
        have hz := CentralIndexFourDerivedBound.center_double_card_le_abelianization_card_of_small_derived
          hQ hd hnonab
        omega
      · have hbcenter := BinarySmallTopCenterBounds.center_le_four hB hBcard hBAb hBab
        have hdim := F.section_invariants_finrank_le_quarter_of_not_elementary N hact hU hnon
        simp only [Nat.card_fin] at hdim
        have hi : Nat.card (F.sectionRepresentation N).invariants ≤ 4 := by
          rw [show Nat.card (F.sectionRepresentation N).invariants =
              2 ^ Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants from by
                simpa only [Nat.card_zmod] using
                  (Module.natCard_eq_pow_finrank (K := ZMod 2)
                    (V := (F.sectionRepresentation N).invariants))]
          exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
        exact ((F.sectionModuleChart N).center_card_le_invariants_mul_center
          (F.zeroCutBase_surjective N)).trans (Nat.mul_le_mul hi hbcenter)
    exact BinaryRankFiveCardUnitBounds.unit_of_card_le_fiveTwelve_center_le_sixteen
      hQ hQrank hQcard hcenter
  · have hlarge : 4 < Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N) := by omega
    have hcenter := F.large_eight_section_center_card_le_four N hact hU hnon (by simp) hlarge
    have hQcard : Nat.card (U ⧸ N) ≤ 2048 := by
      simpa using F.section_order_le_of_finrank_le N 6 32 hsection htop
    exact BinaryRankFiveCardUnitBounds.unit_of_card_le_twoThousand_center_le_four
      hQ hQrank hQcard hcenter

end SymmetricSubgroupAsymptotics.BinaryPairFrame
