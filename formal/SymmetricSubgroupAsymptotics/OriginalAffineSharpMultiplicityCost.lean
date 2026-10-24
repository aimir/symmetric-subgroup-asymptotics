import SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
import SymmetricSubgroupAsymptotics.ActualWreathSharpUniformLocalOrderCost

/-! Original affine costs retaining the translation dimension and actual
complement-quotient prime multiplicity separately, with the sharper
sqrt(5/3) logarithmic coefficient. Valid at every characteristic and top
degree. No permutation-generator premise or local classification is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineSharpMultiplicityCost
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

private theorem rank_le_head_add_quotient (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ ((headCharge J block P i).capacity : ℝ)+
      MarkedC4.genRank (quotientState J block P).A := by
  have hh := ActualWreathElementaryOrdinaryStep.genRank_le_capacity_add_next
    (OriginalBlockOrdinaryCompressionState.initialState J block) (QuotientGroup.mk' P.V)
    (translationChart J block P) (QuotientGroup.mk'_surjective P.V) i
  change MarkedC4.genRank J ≤ (headCharge J block P i).capacity+
    MarkedC4.genRank (quotientState J block P).A at hh
  exact_mod_cast hh

theorem genRank_le_half_cost (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      ((translationDimension J block P : ℝ)+
        (ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V)) : ℝ))*
          (Fintype.card block.Points : ℝ)/2+MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hhead := (headCharge J block P i).half
  simp only [headCharge_dimension] at hhead
  have htail := ActualWreathSharpUniformLocalOrderCost.genRank_le_half_local_cardFactors
    (quotientState J block P) i hI
  change (MarkedC4.genRank (quotientState J block P).A : ℝ) ≤
    (ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V)) : ℝ)*
      (Fintype.card block.Points : ℝ)/2+MarkedC4.genRank block.Top at htail
  have hh := (rank_le_head_add_quotient J block P i).trans (add_le_add hhead htail)
  convert hh using 1 <;> ring

theorem genRank_le_log_cost (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ Real.sqrt (5/3)*
      ((translationDimension J block P : ℝ)+
        (ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V)) : ℝ))*
          (Fintype.card block.Points : ℝ)/
            Real.sqrt (Real.logb 2 (Fintype.card block.Points : ℝ))+
              MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hhead := ElementaryChargeSharpRealLogarithmic.logarithmic_real
    (headCharge J block P i) hI
  simp only [headCharge_dimension] at hhead
  have htail := ActualWreathSharpUniformLocalOrderCost.genRank_le_log_local_cardFactors
    (quotientState J block P) i hI
  change (MarkedC4.genRank (quotientState J block P).A : ℝ) ≤
    Real.sqrt (5/3)*(ArithmeticFunction.cardFactors
      (Nat.card (block.Component ⧸ P.V)) : ℝ)*(Fintype.card block.Points : ℝ)/
        Real.sqrt (Real.logb 2 (Fintype.card block.Points : ℝ))+
          MarkedC4.genRank block.Top at htail
  have hh := (rank_le_head_add_quotient J block P i).trans (add_le_add hhead htail)
  convert hh using 1 <;> ring

end SymmetricSubgroupAsymptotics.OriginalAffineSharpMultiplicityCost
