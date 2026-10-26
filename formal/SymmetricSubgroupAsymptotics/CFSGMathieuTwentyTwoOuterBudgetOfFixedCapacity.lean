import SymmetricSubgroupAsymptotics.AutomorphismCyclicRestrictionCardinality
import SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds

/-! CONDITIONAL internal consumer of a fixed-first-generator capacity.
No such finite capacity is proved here or added to a T1 endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOuterBudgetOfFixedCapacity
open PrimitiveSocleRawStructure CFSGMathieuTwentyTwoElevenGeneration
open OuterFixedElementEvaluationBound

private instance modelFinite : Finite CFSG.Models.Mathieu22 := Finite.of_injective
  (fun g : CFSG.Models.Mathieu22 => g.val) Subtype.val_injective

theorem proper_index_ge_eleven [IsSimpleGroup CFSG.Models.Mathieu22]
    (K : Subgroup CFSG.Models.Mathieu22) (hK : K ≠ ⊤) : 11 ≤ K.index := by
  apply PrimePeriodSimpleQuotientIndex.prime_le_proper_index 11 (by decide) ?_ K hK
  rw [CFSGMathieuTwentyTwoActualOrder.card]
  decide

theorem outer_card_le_eight_of_fixed_capacity [IsSimpleGroup CFSG.Models.Mathieu22]
    (hcapacity : Nat.card (fixedAutomorphisms firstElement) ≤ 44) :
    Nat.card (Outer CFSG.Models.Mathieu22) ≤ 8 := by
  have hh := CFSGMathieuTwentyTwoFixedFirstOuterReduction.outer_mul_eleven_le_twice_fixed
  omega

theorem sufficient_outer_budget_of_fixed_capacity [IsSimpleGroup CFSG.Models.Mathieu22]
    (ell : ℕ) (hell : LeastProperIndex CFSG.Models.Mathieu22 ell)
    (hcapacity : Nat.card (fixedAutomorphisms firstElement) ≤ 44) :
    SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Mathieu22)) := by
  obtain ⟨K,hK,hindex⟩ := hell.1
  have he : 11 ≤ ell := by
    have hi := proper_index_ge_eleven K hK
    omega
  have hout := outer_card_le_eight_of_fixed_capacity hcapacity
  have h8R : (8 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast (show 8 ≤ ell by omega)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 8) h8R
  have hthree : (3 : ℝ) ≤ Real.logb 2 (ell : ℝ) := by
    simpa only [show (8 : ℝ) = (2 : ℝ)^3 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using hlog
  apply SufficientOuterOrderBudget.of_sharp (by omega)
  have houtR : (Nat.card (Outer CFSG.Models.Mathieu22) : ℝ) ≤ 8 := by exact_mod_cast hout
  linarith

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOuterBudgetOfFixedCapacity
