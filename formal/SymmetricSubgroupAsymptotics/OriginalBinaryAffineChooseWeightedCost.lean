import SymmetricSubgroupAsymptotics.ActualWreathChiefChooseDivisorWeights
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineWeightedOrderCost

/-! Exact choose-on-divisor weights on the ORIGINAL binary affine block
embedding. The head is the actual translation chart and the tail is the
SAME actual complement chief trace, whose order divides the literal GL
order. All local capacity obligations are discharged by the actual
induced-module divisor theorem in the concrete exports. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineChooseWeightedCost
open OriginalAffineBlockCharacteristicHead ActualWreathChiefWeightedPrimeBudget
open ActualWreathChooseDivisorCapacity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_weightedCost (hp : P.p = 2) (i : block.Points)
    (weight : ℕ → ℝ) (hw : ∀ p, 1 ≤ weight p)
    (hcap : ∀ (T : ActualWreathCompressionState block.Top block.Points) {D' : Type}
      [Group D'] [Finite D'] (phi : T.D →* D') (C : ElementaryMinimalNormalChart phi.ker),
      (ActualWreathElementaryOrdinaryStep.layerCapacity T phi C i : ℝ) ≤
        (Module.finrank (ZMod C.p) C.V : ℝ)*weight C.p) :
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ)*weight 2 +
      weightedOrder weight (Nat.card (Matrix.GeneralLinearGroup
        (Fin (translationDimension J block P)) (ZMod 2))) + MarkedC4.genRank block.Top := by
  obtain ⟨c,hc,_,hhead,hrank⟩ := exists_translation_head_and_tail J block P i
  have htail := ActualWreathChiefLayerWeightBudget.cost_le_weightedOrder hc weight hw hcap
  have htail' := htail.trans (weightedOrder_mono_of_dvd weight
    (fun p => le_trans (by norm_num) (hw p))
    (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
    (Nat.card_pos (α := Matrix.GeneralLinearGroup
      (Fin (translationDimension J block P)) (ZMod 2))).ne'
    (OriginalBinaryAffineJointCharacteristicCost.translation_quotient_card_dvd_GL J block P hp))
  have hhc := hcap (OriginalBlockOrdinaryCompressionState.initialState J block)
    (QuotientGroup.mk' P.V) (translationChart J block P)
  change ((headCharge J block P i).capacity : ℝ) ≤
    ((headCharge J block P i).dimension : ℝ)*weight (headCharge J block P i).p at hhc
  simp only [headCharge_prime,headCharge_dimension,hp] at hhc
  have hrankR : (MarkedC4.genRank J : ℝ) ≤
      ((headCharge J block P i).capacity : ℝ) + (c : ℝ) + MarkedC4.genRank block.Top := by
    exact_mod_cast hrank
  linarith

theorem genRank_le_divisorWeight (hp : P.p = 2) (i : block.Points)
    (q e : ℕ) (hq : q.Prime) (hd : q^e ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ)*
      divisorWeight (Fintype.card block.Points) q e 2 +
      weightedOrder (divisorWeight (Fintype.card block.Points) q e)
        (Nat.card (Matrix.GeneralLinearGroup
          (Fin (translationDimension J block P)) (ZMod 2))) + MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  apply genRank_le_weightedCost J block P hp i _ (one_le_divisorWeight _ q e)
  intro T D' _ _ phi C
  exact layerCapacity_le_divisorWeight T phi C i hI q e hq hd

theorem genRank_le_min_divisorWeights (hp : P.p = 2) (i : block.Points)
    (q e r f : ℕ) (hq : q.Prime) (hd : q^e ∣ Fintype.card block.Points)
    (hr : r.Prime) (hrd : r^f ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ)*
      min (divisorWeight (Fintype.card block.Points) q e 2)
        (divisorWeight (Fintype.card block.Points) r f 2) +
      weightedOrder (fun p => min (divisorWeight (Fintype.card block.Points) q e p)
        (divisorWeight (Fintype.card block.Points) r f p))
        (Nat.card (Matrix.GeneralLinearGroup
          (Fin (translationDimension J block P)) (ZMod 2))) + MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  apply genRank_le_weightedCost J block P hp i
    (fun p => min (divisorWeight (Fintype.card block.Points) q e p)
      (divisorWeight (Fintype.card block.Points) r f p))
  · intro p
    exact le_min (one_le_divisorWeight _ q e p) (one_le_divisorWeight _ r f p)
  · intro T D' _ _ phi C
    exact ActualWreathChiefChooseDivisorWeights.layerCapacity_le_min_divisorWeights
      T phi C i hI q e r f hq hd hr hrd


end SymmetricSubgroupAsymptotics.OriginalBinaryAffineChooseWeightedCost
