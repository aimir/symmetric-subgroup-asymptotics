import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval
import SymmetricSubgroupAsymptotics.PreE7FiniteMixedPermutationMenu

/-! Original-weight numerics for a two-slot sixteen-point interval with
an eight-point retained comparator. Coefficients use the existing uniform
permutation menu, with no supplied normal census or final estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.SixteenPointSemanticEightComparatorNumerics
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem tail_bound (hMN : McIverNeumannPermutationGeneratorBound)
    (U : Subgroup (Equiv.Perm (Fin 16))) (D : CompleteCharacterIntervalData U) :
    D.tailConstant≤(2 : ℝ)^(1024 : ℕ) := by
  letI : Fintype {N : Subgroup U // N.Normal} := Subtype.fintype Subgroup.Normal
  let Below := {N : {N : Subgroup U // N.Normal} // ¬ D.E≤N.1}
  have hcard : Nat.card Below≤2^512 :=
    (Nat.card_le_card_of_injective
      (fun N : Below => N.val) Subtype.val_injective).trans
      (PreE7FiniteMixedPermutationMenu.state_card_le hMN U FiniteNormalStateRegistry.allNormals)
  unfold CompleteCharacterIntervalData.tailConstant
  change (∑ N : Below, (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ))≤_
  calc
    _≤∑ _N : Below, (2 : ℝ)^(512 : ℕ) := by
      apply Finset.sum_le_sum
      intro N _
      letI := N.1.2
      exact_mod_cast PreE7FiniteMixedPermutationMenu.quotient_aut_card_le hMN U N.1.1
    _=(Nat.card Below : ℝ)*(2 : ℝ)^(512 : ℕ) := by
      simp [Nat.card_eq_fintype_card]
    _≤(2 : ℝ)^(512 : ℕ)*(2 : ℝ)^(512 : ℕ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _=(2 : ℝ)^(1024 : ℕ) := by rw [← pow_add]

/-- Only literal structural fields2 and8 are supplied; all numerical
inequalities and the full original normal-axis sum are proved here. -/
def numerics (hMN : McIverNeumannPermutationGeneratorBound)
    {i : PreE7NonPairActionClass 16}
    (D : SocleGeneratorCharacterIntervalData (preE7NonPairAction 16 i))
    (hs : D.slots=2) (hd : D.quotientDegree=8)
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7CompleteCharacterIntervalNumerics (D.toCompleteCharacterIntervalData hZmud) where
  comparator_margin := by
    change preE7CharacterRho*(16 : ℝ)≤
      ((evenWidth 16 : ℝ)-(max 2 D.quotientDegree : ℕ))/8
    rw [hd]
    norm_num [preE7CharacterRho,evenWidth,halfDegree]
  theta_window := by
    change (D.slots : ℝ)*(Real.logb 2 5/3)≤preE7CharacterWindow 16
    rw [hs]
    have hlog := logb_two_five_div_five_lt_seven_fifteenths
    norm_num [preE7CharacterWindow,preE7CharacterRho,halfDegree]
    nlinarith
  tail_total_bound b :=
    (tail_bound hMN _ (D.toCompleteCharacterIntervalData hZmud)).trans
      (PreE7FiniteMixedPermutationMenu.allowance b)

/-- Direct original-weight rank-tail source; the retained complete quotient
weight is charged once by the existing character-interval theorem. -/
def source (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    {i : PreE7NonPairActionClass 16}
    (D : SocleGeneratorCharacterIntervalData (preE7NonPairAction 16 i))
    (hs : D.slots=2) (hd : D.quotientDegree=8) :
    PreE7RankTailSourceOrYonedaTopData 16 i :=
  (numerics hMN D hs hd hZmud).toRankTailSourceOrYonedaTop lit family

end SymmetricSubgroupAsymptotics.SixteenPointSemanticEightComparatorNumerics
