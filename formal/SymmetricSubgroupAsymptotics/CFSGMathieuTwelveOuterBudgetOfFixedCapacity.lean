import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualEquivalence
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveRecoveredPairRelations
import SymmetricSubgroupAsymptotics.PrimeCyclicSylowFixedFibreOuterBound
import SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex
import SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexBounds
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Internal consumer of a genuine original-M12 fixed-A capacity.
The weak Sylow-normalizer factor gives22*|Out|≤10*|Aut_A|, so capacity24
suffices for |Out|≤10. Since every proper index is at least11, the cube
inequality2^10≤11^3 supplies the sharp coefficient-three outer budget.
The capacity argument must be discharged by complete finite certificates;
this conditional leaf adds no T1 facade premise or parity assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBudgetOfFixedCapacity
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveRecoveredPairRelations PrimitiveSocleRawStructure
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem firstElement_cycleType : firstElement.val.cycleType = {11} := by
  change (x.val * y.val).cycleType = _
  rw [x_coe_eq,y_coe_eq]
  decide +kernel

theorem firstElement_order : orderOf firstElement = 11 := by
  have h : orderOf firstElement.val = 11 := by
    rw [←Equiv.Perm.lcm_cycleType,firstElement_cycleType]
    simp
  exact (orderOf_injective M12Subgroup.subtype Subtype.val_injective firstElement).symm.trans h

theorem original_noncommutative : ¬IsMulCommutative M12 := by
  have hmove : (xPermutation * yPermutation) (0 : Fin 12) ≠
      (yPermutation * xPermutation) (0 : Fin 12) := by decide +kernel
  intro h
  letI : IsMulCommutative M12 := h
  have he := congrArg M12Subgroup.subtype (mul_comm' x y)
  change x.val * y.val = y.val * x.val at he
  rw [x_coe_eq,y_coe_eq] at he
  exact hmove (congrArg (fun σ : Perm12 => σ (0 : Fin 12)) he)

theorem original_outer_mul_twentyTwo_le_ten_fixed
    [IsSimpleGroup CFSG.Models.Presentations.M12.Model] :
    22 * Nat.card (Outer M12) ≤
      10 * Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms firstElement) := by
  letI : Finite M12 := Finite.of_injective
    (fun g : M12 => (g : Perm12)) Subtype.val_injective
  let e : CFSG.Models.Presentations.M12.Model ≃* M12 :=
    CFSGMathieuTwelveActualEquivalence.actualEquivalence
  letI : IsSimpleGroup M12 := e.symm.isSimpleGroup
  have hnot : ¬(11 : ℕ)^2 ∣ Nat.card M12 := by
    rw [M12Cardinality.card_M12]
    decide
  have hU : IsPGroup 11 (Subgroup.zpowers firstElement) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,firstElement_order,pow_one]
  obtain ⟨P,hP⟩ := hU.exists_le_sylow
  have hmember : firstElement ∈ P := hP (Subgroup.mem_zpowers firstElement)
  have hcard : Nat.card P = 11 :=
    SimpleInvolutionPrimeCycleGoodSylow.sylow_card_of_member_order
      P firstElement hmember firstElement_order hnot
  have heq : (P : Subgroup M12) = Subgroup.zpowers firstElement := by
    apply (Subgroup.eq_of_le_of_card_ge hP ?_).symm
    simpa only [Nat.card_zpowers,firstElement_order,hcard] using (Nat.le_refl 11)
  have hw := PrimeCyclicSylowFixedFibreOuterBound.twice_prime_mul_outer_le_pred_mul_fixed
    original_noncommutative P hcard firstElement heq
  change 22 * Nat.card (Outer M12) ≤
    10 * Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms firstElement) at hw
  exact hw

theorem original_outer_card_le_ten
    [IsSimpleGroup CFSG.Models.Presentations.M12.Model]
    (hcapacity : Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms firstElement) ≤ 24) :
    Nat.card (Outer M12) ≤ 10 := by
  have hw := original_outer_mul_twentyTwo_le_ten_fixed
  omega

theorem outer_card_le_ten [IsSimpleGroup CFSG.Models.Presentations.M12.Model]
    (hcapacity : Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms firstElement) ≤ 24) :
    Nat.card (Outer CFSG.Models.Presentations.M12.Model) ≤ 10 := by
  rw [CFSGReduction.outer_card_congr CFSGMathieuTwelveActualEquivalence.actualEquivalence]
  exact original_outer_card_le_ten hcapacity

theorem proper_index_ge_eleven [Finite CFSG.Models.Presentations.M12.Model]
    [IsSimpleGroup CFSG.Models.Presentations.M12.Model]
    (H : Subgroup CFSG.Models.Presentations.M12.Model) (hH : H ≠ ⊤) : 11 ≤ H.index := by
  apply PrimePeriodSimpleQuotientIndex.prime_le_proper_index 11
    (by decide : Nat.Prime 11) ?_ H hH
  rw [CFSGMathieuTwelveActualEquivalence.card]
  decide

theorem least_index_ge_eleven [Finite CFSG.Models.Presentations.M12.Model]
    [IsSimpleGroup CFSG.Models.Presentations.M12.Model] (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Presentations.M12.Model ell) : 11 ≤ ell := by
  obtain ⟨H,hH,hindex⟩ := hell.1
  rw [←hindex]
  exact proper_index_ge_eleven H hH

theorem ten_le_three_logb (ell : ℕ) (hell : 11 ≤ ell) :
    (10 : ℝ) ≤ 3 * Real.logb 2 ell := by
  have hpow : (2 : ℝ)^10 ≤ (ell : ℝ)^3 := by
    exact_mod_cast ((by decide : (2 : ℕ)^10 ≤ 11^3).trans (Nat.pow_le_pow_left hell 3))
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2^10) hpow
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one,Nat.cast_ofNat] using hl

theorem sufficient_outer_budget [Finite CFSG.Models.Presentations.M12.Model]
    [IsSimpleGroup CFSG.Models.Presentations.M12.Model]
    (hcapacity : Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms firstElement) ≤ 24)
    (ell : ℕ) (hell : LeastProperIndex CFSG.Models.Presentations.M12.Model ell) :
    SufficientOuterOrderBudget ell (Nat.card (Outer CFSG.Models.Presentations.M12.Model)) := by
  have he := least_index_ge_eleven ell hell
  have hout : (Nat.card (Outer CFSG.Models.Presentations.M12.Model) : ℝ) ≤ 10 := by
    exact_mod_cast outer_card_le_ten hcapacity
  exact SufficientOuterOrderBudget.of_sharp (by omega) (hout.trans (ten_le_three_logb ell he))

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveOuterBudgetOfFixedCapacity
