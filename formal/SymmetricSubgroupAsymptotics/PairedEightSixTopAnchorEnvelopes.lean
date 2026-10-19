import SymmetricSubgroupAsymptotics.PairedEightModuleTwoTernaryCard
import SymmetricSubgroupAsymptotics.TernaryOddPartTopAnchorEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCompleteCatalogue

/-! Only the six natural-module-capacity-two tops need the sharper anchored
cost. This file binds that cost on EVERY actual nonbinary normal quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

def IsModuleTwoRow (j : Fin 24) : Prop :=
  j=0 ∨ j=1 ∨ j=5 ∨ j=10 ∨ j=11 ∨ j=14

theorem moduleTwoRow_card (j : Fin 24) (hj : IsModuleTwoRow j) :
    ∃ a : ℕ, Nat.card (interface j).top=2^a*3 := by
  rcases hj with h|h|h|h|h|h
  · subst j; exact ⟨3,top1_ternary_card⟩
  · subst j; exact ⟨3,top2_ternary_card⟩
  · subst j; exact ⟨4,top6_ternary_card⟩
  · subst j; exact ⟨3,top11_ternary_card⟩
  · subst j; exact ⟨5,top12_ternary_card⟩
  · subst j; exact ⟨6,top15_ternary_card⟩

/-- The literal denominator is unchanged; no normal-menu completeness
claim is inferred from a metadata list. -/
def moduleTwoRow_nonbinary_quotient_envelope
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (j : Fin 24) (hj : IsModuleTwoRow j)
    (N : Subgroup (interface j).top) [N.Normal]
    (hQ : ¬IsPGroup 2 ((interface j).top ⧸ N)) :
    DegreeTwoPairRelativeQuotientEnvelope ((interface j).top ⧸ N)
      (degreeTwoPairOrdinaryRelativeProfile 1 1) := by
  let witness := moduleTwoRow_card j hj
  let a := witness.choose
  have ha : Nat.card (interface j).top=2^a*3 := witness.choose_spec
  have hd : Nat.card ((interface j).top ⧸ N) ∣ 2^a*3 := by
    rw [←ha]
    exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
  exact ternaryOddPart_top_anchor_envelope hZmud lit hd hQ
    ((DegreeTwoPairedEightCompleteCatalogue.completeRow j).topSocle ⟨N,inferInstance⟩)

end DegreeTwoPairedEightSharedTops
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
