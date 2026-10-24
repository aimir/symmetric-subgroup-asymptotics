import SymmetricSubgroupAsymptotics.ActualWreathChiefDivisorWeights
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointCharacteristicCost
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearTotalPrimeMultiplicity
import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorNumerics

/-! Arbitrary-top weighted ordinary costs on the ORIGINAL binary affine
block action. The actual quotient order divides its faithful binary GL
order. Constructed divisor weights retain characteristic information;
the uniform half/log specializations give a dimension-squared aggregate.
The actual top rank remains explicit, with no global Tracey/MN input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineWeightedOrderCost
open OriginalAffineBlockCharacteristicHead ActualWreathCharacteristicChiefProfile
open ActualWreathChiefWeightedPrimeBudget ActualWreathChiefDivisorWeights

theorem weightedOrder_const (c : ℝ) (M : ℕ) :
    weightedOrder (fun _ => c) M = (ArithmeticFunction.cardFactors M : ℝ)*c := by
  simp only [weightedOrder,ArithmeticFunction.cardFactors_eq_sum_factorization,
    Finsupp.sum,Nat.cast_sum,Finset.sum_mul]

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
    (hcap : ∀ c : ElementaryCharge (Fintype.card block.Points),
      (c.capacity : ℝ) ≤ (c.dimension : ℝ)*weight c.p) :
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ)*weight 2 +
      weightedOrder weight (Nat.card (Matrix.GeneralLinearGroup
        (Fin (translationDimension J block P)) (ZMod 2))) + MarkedC4.genRank block.Top := by
  obtain ⟨c,hc,_,hhead,hrank⟩ := exists_translation_head_and_tail J block P i
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have htail := cost_le_weightedOrder hc hI weight hw hcap
  have htail' := htail.trans (weightedOrder_mono_of_dvd weight
    (fun p => le_trans (by norm_num) (hw p))
    (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
    (Nat.card_pos (α := Matrix.GeneralLinearGroup
      (Fin (translationDimension J block P)) (ZMod 2))).ne'
    (OriginalBinaryAffineJointCharacteristicCost.translation_quotient_card_dvd_GL J block P hp))
  have hhc := hcap (headCharge J block P i)
  simp only [headCharge_prime,headCharge_dimension,hp] at hhc
  have hrankR : (MarkedC4.genRank J : ℝ) ≤
      ((headCharge J block P i).capacity : ℝ) + (c : ℝ) + MarkedC4.genRank block.Top := by
    exact_mod_cast hrank
  linarith

theorem genRank_le_divisorWeight (hp : P.p = 2) (i : block.Points)
    (q e : ℕ) (hq : q.Prime) (he : 1 ≤ e) (hd : q^e ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ)*
      divisorWeight (Fintype.card block.Points) q e 2 +
      weightedOrder (divisorWeight (Fintype.card block.Points) q e)
        (Nat.card (Matrix.GeneralLinearGroup
          (Fin (translationDimension J block P)) (ZMod 2))) + MarkedC4.genRank block.Top := by
  exact genRank_le_weightedCost J block P hp i _ (one_le_divisorWeight _ q e)
    (fun c => capacity_le_divisorWeight c q e hq he hd)

theorem genRank_le_min_divisorWeights (hp : P.p = 2) (i : block.Points)
    (q e r f : ℕ) (hq : q.Prime) (he : 1 ≤ e) (hd : q^e ∣ Fintype.card block.Points)
    (hr : r.Prime) (hf : 1 ≤ f) (hrd : r^f ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ)*
      min (divisorWeight (Fintype.card block.Points) q e 2)
        (divisorWeight (Fintype.card block.Points) r f 2) +
      weightedOrder (fun p => min (divisorWeight (Fintype.card block.Points) q e p)
        (divisorWeight (Fintype.card block.Points) r f p))
        (Nat.card (Matrix.GeneralLinearGroup
          (Fin (translationDimension J block P)) (ZMod 2))) + MarkedC4.genRank block.Top := by
  apply genRank_le_weightedCost J block P hp i
    (fun p => min (divisorWeight (Fintype.card block.Points) q e p)
      (divisorWeight (Fintype.card block.Points) r f p))
  · intro p
    exact le_min (one_le_divisorWeight _ q e p) (one_le_divisorWeight _ r f p)
  · intro c
    exact capacity_le_min_divisorWeights c q e r f hq he hd hr hf hrd

private theorem uniform_cost (hp : P.p = 2) (i : block.Points)
    (rate : ℝ) (hrate : 1 ≤ rate)
    (hcap : ∀ c : ElementaryCharge (Fintype.card block.Points),
      (c.capacity : ℝ) ≤ (c.dimension : ℝ)*rate) :
    (MarkedC4.genRank J : ℝ) ≤ (translationDimension J block P : ℝ)^2*rate +
      MarkedC4.genRank block.Top := by
  have hh := genRank_le_weightedCost J block P hp i (fun _ => rate) (fun _ => hrate) hcap
  rw [weightedOrder_const] at hh
  have hd := BinaryGeneralLinearTotalPrimeMultiplicity.dimension_add_GL_cardFactors_le_sq
    (translationDimension J block P)
  have hdR : (translationDimension J block P : ℝ) +
      ArithmeticFunction.cardFactors (Nat.card (Matrix.GeneralLinearGroup
        (Fin (translationDimension J block P)) (ZMod 2))) ≤
        (translationDimension J block P : ℝ)^2 := by exact_mod_cast hd
  have hm := mul_le_mul_of_nonneg_right hdR (show 0 ≤ rate by linarith)
  nlinarith

theorem genRank_le_half_cost (hp : P.p = 2) (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      (translationDimension J block P : ℝ)^2*(Fintype.card block.Points : ℝ)/2 +
        MarkedC4.genRank block.Top := by
  have ht : (2 : ℝ) ≤ Fintype.card block.Points := by
    exact_mod_cast (show 2 ≤ Fintype.card block.Points by
      simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)
  have hh := uniform_cost J block P hp i ((Fintype.card block.Points : ℝ)/2)
    (by linarith) (fun c => by simpa only [mul_div_assoc] using c.half)
  simpa only [mul_div_assoc] using hh

theorem genRank_le_log_cost (hp : P.p = 2) (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      2*(translationDimension J block P : ℝ)^2*(Fintype.card block.Points : ℝ)/
        Real.sqrt (Real.logb 2 (Fintype.card block.Points : ℝ)) +
          MarkedC4.genRank block.Top := by
  let t : ℝ := Fintype.card block.Points
  have ht : 2 ≤ t := by
    dsimp only [t]
    exact_mod_cast (show 2 ≤ Fintype.card block.Points by
      simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2)
  have hL : 0 < Real.logb 2 t := Real.logb_pos (by norm_num) (by linarith)
  have hs : 0 < Real.sqrt (Real.logb 2 t) := Real.sqrt_pos.mpr hL
  have hsle : Real.sqrt (Real.logb 2 t) ≤ t :=
    (Real.sqrt_le_iff).mpr ⟨by linarith,LargeOrbitGeneratorNumerics.logb_le_square ht⟩
  have hunit : (1 : ℝ) ≤ t/Real.sqrt (Real.logb 2 t) :=
    (le_div_iff₀ hs).mpr (by simpa using hsle)
  have hrate : (1 : ℝ) ≤ 2*t/Real.sqrt (Real.logb 2 t) := by
    calc
      1 ≤ t/Real.sqrt (Real.logb 2 t) := hunit
      _ ≤ 2*(t/Real.sqrt (Real.logb 2 t)) := by linarith only [hunit]
      _ = 2*t/Real.sqrt (Real.logb 2 t) := by ring
  have hh := uniform_cost J block P hp i (2*t/Real.sqrt (Real.logb 2 t))
    hrate (fun c => by convert c.logarithmic using 1 <;> dsimp [t] <;> ring)
  convert hh using 1 <;> dsimp [t] <;> ring

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineWeightedOrderCost
