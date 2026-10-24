import SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
import SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost

/-! Tame uniform costs on the original affine block action, at every
profile prime. The literal translation head costs its actual dimension d,
not log₂|V|. Only the SAME compressed quotient is charged to its genuine
order, at most p^(d²). This retains d(1+log₂r), which is smaller than the
whole-component order bound. No permutation-generator input is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalAffineTameUniformCost
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem quotient_log_le_dimension_mul_degree_log :
    Real.logb 2 (Nat.card (block.Component ⧸ P.V) : ℝ) ≤
      (translationDimension J block P : ℝ)*Real.logb 2 (Nat.card block.Fibre : ℝ) := by
  let d := translationDimension J block P
  have hcard := translation_quotient_card_le J block P
  have hcardR : (Nat.card (block.Component ⧸ P.V) : ℝ) ≤ (P.p : ℝ)^(d^2) := by
    exact_mod_cast hcard
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (Nat.card_pos (α := block.Component ⧸ P.V))) hcardR
  have hr : (Nat.card block.Fibre : ℝ) = (P.p : ℝ)^d := by
    exact_mod_cast (fibre_card_eq_prime_pow_dimension J block P)
  calc
    Real.logb 2 (Nat.card (block.Component ⧸ P.V) : ℝ) ≤
        ((d^2 : ℕ) : ℝ)*Real.logb 2 (P.p : ℝ) := by
      simpa only [Real.logb_pow] using hh
    _ = (translationDimension J block P : ℝ)*Real.logb 2 (Nat.card block.Fibre : ℝ) := by
      rw [hr,Real.logb_pow,Nat.cast_pow]
      change (d : ℝ)^2*Real.logb 2 (P.p : ℝ) =
        (d : ℝ)*((d : ℝ)*Real.logb 2 (P.p : ℝ))
      ring

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
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ)*
      (1+Real.logb 2 (Nat.card block.Fibre : ℝ))*(Fintype.card block.Points : ℝ)/2+
        MarkedC4.genRank block.Top := by
  let d := translationDimension J block P
  let t : ℝ := Fintype.card block.Points
  let s := Real.logb 2 (Nat.card block.Fibre : ℝ)
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hhead : ((headCharge J block P i).capacity : ℝ) ≤ (d : ℝ)*t/2 := by
    simpa only [headCharge_dimension] using (headCharge J block P i).half
  have htail := ActualWreathUniformLocalOrderCost.genRank_le_half_local_log
    (quotientState J block P) i hI
  change (MarkedC4.genRank (quotientState J block P).A : ℝ) ≤
    Real.logb 2 (Nat.card (block.Component ⧸ P.V) : ℝ)*t/2+MarkedC4.genRank block.Top at htail
  have horder := quotient_log_le_dimension_mul_degree_log J block P
  have hmul := mul_le_mul_of_nonneg_right horder (show 0 ≤ t/2 by positivity)
  have htail' : (MarkedC4.genRank (quotientState J block P).A : ℝ) ≤
      (d : ℝ)*s*t/2+MarkedC4.genRank block.Top := by
    have hm : Real.logb 2 (Nat.card (block.Component ⧸ P.V) : ℝ)*t/2 ≤ (d : ℝ)*s*t/2 := by
      convert hmul using 1 <;> dsimp only [d,s] <;> ring
    exact htail.trans (add_le_add hm le_rfl)
  have hh := (rank_le_head_add_quotient J block P i).trans (add_le_add hhead htail')
  convert hh using 1 <;> dsimp only [d,t,s] <;> ring

theorem genRank_le_log_cost (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ 2*(translationDimension J block P : ℝ)*
      (1+Real.logb 2 (Nat.card block.Fibre : ℝ))*(Fintype.card block.Points : ℝ)/
        Real.sqrt (Real.logb 2 (Fintype.card block.Points : ℝ))+MarkedC4.genRank block.Top := by
  let d := translationDimension J block P
  let t : ℝ := Fintype.card block.Points
  let s := Real.logb 2 (Nat.card block.Fibre : ℝ)
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hhead : ((headCharge J block P i).capacity : ℝ) ≤
      2*(d : ℝ)*t/Real.sqrt (Real.logb 2 t) := by
    simpa only [headCharge_dimension] using (headCharge J block P i).logarithmic
  have htail := ActualWreathUniformLocalOrderCost.genRank_le_log_local_log
    (quotientState J block P) i hI
  change (MarkedC4.genRank (quotientState J block P).A : ℝ) ≤
    2*Real.logb 2 (Nat.card (block.Component ⧸ P.V) : ℝ)*t/Real.sqrt (Real.logb 2 t)+
      MarkedC4.genRank block.Top at htail
  have horder := quotient_log_le_dimension_mul_degree_log J block P
  have hmul := mul_le_mul_of_nonneg_right horder
    (show 0 ≤ 2*t/Real.sqrt (Real.logb 2 t) by positivity)
  have htail' : (MarkedC4.genRank (quotientState J block P).A : ℝ) ≤
      2*(d : ℝ)*s*t/Real.sqrt (Real.logb 2 t)+MarkedC4.genRank block.Top := by
    have hm : 2*Real.logb 2 (Nat.card (block.Component ⧸ P.V) : ℝ)*t/Real.sqrt (Real.logb 2 t) ≤
        2*(d : ℝ)*s*t/Real.sqrt (Real.logb 2 t) := by
      convert hmul using 1 <;> dsimp only [d,s] <;> ring
    exact htail.trans (add_le_add hm le_rfl)
  have hh := (rank_le_head_add_quotient J block P i).trans (add_le_add hhead htail')
  convert hh using 1 <;> dsimp only [d,t,s] <;> ring

end SymmetricSubgroupAsymptotics.OriginalAffineTameUniformCost
