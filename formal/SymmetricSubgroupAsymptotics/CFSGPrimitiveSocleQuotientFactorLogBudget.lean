import SymmetricSubgroupAsymptotics.CFSGUniformOuterLogBudget
import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget
import SymmetricSubgroupAsymptotics.PrimitiveSocleStrictOuterOrdinaryRecurrence

/-! The ACTUAL local socle quotient has uniformly polylogarithmic order.
No numerical simple-model callback or order formula is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveSocleQuotientFactorLogBudget
open PrimitiveSocleRawStructure CFSGReduction

theorem exists_uniform_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ B : ℕ, 1≤B ∧ ∀ {R X : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
      (D : NonaffineData R X),
      ((Nat.log 2 (Nat.card (R ⧸ finiteGroupSocle R))+1 : ℕ) : ℝ)≤
        (B : ℝ)*D.factorCount*Real.logb 2 (Nat.card X : ℝ) := by
  obtain ⟨B,hB,houter⟩ := CFSGUniformOuterLogBudget.exists_uniform_degree_outer_log_budget hCFSG
  refine ⟨B+2,by omega,?_⟩
  intro R X _ _ _ _ D
  let L := Real.logb 2 (Nat.card X : ℝ)
  have hk0 : (0 : ℝ)≤D.factorCount := Nat.cast_nonneg _
  have hkl : (D.factorCount : ℝ)≤L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (pow_pos (by norm_num : (0 : ℝ)<2) D.factorCount)
      (show (2 : ℝ)^D.factorCount≤Nat.card X by
        exact_mod_cast FiniteModelPrimitiveOrdinaryBudget.two_pow_factorCount_le_degree D)
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] using hh
  have hL : 0≤L := hk0.trans hkl
  have hcard := Nat.le_of_dvd
    (mul_pos (pow_pos (Nat.card_pos (α := Outer D.Simple)) D.factorCount)
      (Nat.factorial_pos D.factorCount))
    (PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_card_dvd_outer_wreath D)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by exact_mod_cast Nat.card_pos (α := R ⧸ finiteGroupSocle R) :
      (0 : ℝ)<Nat.card (R ⧸ finiteGroupSocle R)) (by exact_mod_cast hcard :
      (Nat.card (R ⧸ finiteGroupSocle R) : ℝ)≤
        (Nat.card (Outer D.Simple) : ℝ)^D.factorCount * D.factorCount.factorial)
  have ho : (0 : ℝ)<Nat.card (Outer D.Simple) := by exact_mod_cast Nat.card_pos (α := Outer D.Simple)
  have hf : (0 : ℝ)<D.factorCount.factorial := by exact_mod_cast Nat.factorial_pos D.factorCount
  rw [Real.logb_mul (ne_of_gt (pow_pos ho _)) (ne_of_gt hf),Real.logb_pow] at hlog
  have hout := houter D
  have hfac := CFSGCoarsePrimitiveNumerics.factorial_logb_le_square D.factorCount
  have hmul := mul_le_mul_of_nonneg_left hout hk0
  have hfacprod : (D.factorCount : ℝ)^2≤(D.factorCount : ℝ)*L := by
    nlinarith [mul_le_mul_of_nonneg_left hkl hk0]
  have hk1 : (1 : ℝ)≤D.factorCount := by
    exact_mod_cast (show 1≤D.factorCount by have hh := D.factorCount_pos; omega)
  have hL1 : 1≤L := hk1.trans hkl
  have hprod1 : (1 : ℝ)≤(D.factorCount : ℝ)*L :=
    one_le_mul_of_one_le_of_one_le hk1 hL1
  have hnatlog := Real.natLog_le_logb (Nat.card (R ⧸ finiteGroupSocle R)) 2
  dsimp [L] at *
  push_cast
  nlinarith

end SymmetricSubgroupAsymptotics.CFSGPrimitiveSocleQuotientFactorLogBudget
