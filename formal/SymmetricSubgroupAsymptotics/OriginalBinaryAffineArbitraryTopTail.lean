import SymmetricSubgroupAsymptotics.OriginalBinaryAffineWeightedOrderCost
import SymmetricSubgroupAsymptotics.BinaryAffineArbitraryTopRealTail

/-! The ORIGINAL binary affine block step in every dimension at least7,
for arbitrary actual top degree. Only the genuine smaller-top coarse
ceiling is retained. No current-degree Tracey/MN, solvability, CFSG,
simple-generation, or local-model classification premise is imposed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineArbitraryTopTail
open OriginalAffineBlockCharacteristicHead OriginalBinaryAffineWeightedOrderCost

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem genRank_le_ceiling_of_dimension_ge_seven (hp : P.p = 2)
    (hd : 7 ≤ translationDimension J block P) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let d := translationDimension J block P
  let t := Nat.card block.Points
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hh := genRank_le_half_cost J block P hp i
  have hl := genRank_le_log_cost J block P hp i
  simp only [Fintype.card_eq_nat_card] at hh hl
  have htopR : (MarkedC4.genRank block.Top : ℝ) ≤
      (traceyPermutationGeneratorCeiling t : ℝ) := by exact_mod_cast htop
  change (MarkedC4.genRank block.Top : ℝ) ≤
    (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) at htopR
  have hhalf : (MarkedC4.genRank J : ℝ) ≤ (d : ℝ)^2*(t : ℝ)/2 +
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) := by
    exact hh.trans (add_le_add le_rfl htopR)
  have hlog : (MarkedC4.genRank J : ℝ) ≤ 2*(d : ℝ)^2*(t : ℝ)/
      Real.sqrt (Real.logb 2 (t : ℝ)) +
        (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) := by
    exact hl.trans (add_le_add le_rfl htopR)
  have hreal := BinaryAffineArbitraryTopRealTail.aggregate_le d hd (t : ℝ)
    (MarkedC4.genRank J : ℝ) htR hhalf hlog
  have hn : n = 2^d*t := by
    calc
      n = Nat.card block.Fibre * Nat.card block.Points := by
        simpa only [Nat.card_fin] using block.degree_product.symm
      _ = 2^d*t := by rw [fibre_card_eq_prime_pow_dimension J block P,hp]
  have hnR : (n : ℝ) = (2 : ℝ)^d*(t : ℝ) := by exact_mod_cast hn
  have hlogn : Real.logb 2 (n : ℝ) = (d : ℝ)+Real.logb 2 (t : ℝ) := by
    rw [hnR,Real.logb_mul (by positivity : (2 : ℝ)^d ≠ 0)
      (by exact_mod_cast (show t ≠ 0 by omega)),Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
  have htarget : (MarkedC4.genRank J : ℝ) ≤
      (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
    rw [hlogn, hnR]
    exact hreal
  have hfinal := htarget.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hfinal
  exact_mod_cast hfinal

theorem exists_generating_finset (hp : P.p = 2)
    (hd : 7 ≤ translationDimension J block P) (i : block.Points)
    (htop : MarkedC4.genRank block.Top ≤
      traceyPermutationGeneratorCeiling (Nat.card block.Points)) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := J)
  exact ⟨S,hgen,hS.le.trans (genRank_le_ceiling_of_dimension_ge_seven
    J block P hp hd i htop)⟩

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineArbitraryTopTail
