import SymmetricSubgroupAsymptotics.ActualPrimitiveSocleLogSizeBounds
import SymmetricSubgroupAsymptotics.CFSGSimpleAutomorphismPolylogBudget

/-! Uniform automorphism logarithm bound for the SAME actual local simple
factor; the actual faithful action bounds its order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGActualSimpleAutomorphismLogBudget
open PrimitiveSocleRawStructure

theorem exists_uniform_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, 1≤A ∧ ∀ {R X : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
      [FaithfulSMul R X] (D : NonaffineData R X) (hr : 2≤Nat.card X),
      Real.logb 2 (Nat.card (D.Simple ≃* D.Simple) : ℝ)≤
        (A : ℝ)*(Nat.card X : ℝ)*(Real.logb 2 (Nat.card X : ℝ))^3 := by
  obtain ⟨A,hA⟩ := CFSGSimpleAutomorphismPolylogBudget.exists_uniform_automorphism_budget hCFSG
  refine ⟨9*A+1,by omega,?_⟩
  intro R X _ _ _ _ _ D hr
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  let L := Real.logb 2 (Nat.card X : ℝ)
  have hk1 : (1 : ℝ)≤D.factorCount := by
    exact_mod_cast (show 1≤D.factorCount by have hh := D.factorCount_pos; omega)
  have hL1 : 1≤L := hk1.trans (ActualPrimitiveSocleLogSizeBounds.factorCount_le_log D)
  have hL0 : 0≤L := by linarith
  have hT0 : 0≤Real.logb 2 (Nat.card D.Simple : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (Nat.card_pos (α := D.Simple)))
  have hT : Real.logb 2 (Nat.card D.Simple : ℝ)≤(Nat.card X : ℝ)*L :=
    (le_mul_of_one_le_left hT0 hk1).trans (ActualPrimitiveSocleLogSizeBounds.socle_log_le D hr)
  have hellr := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hnatr : (Nat.log 2 ell : ℝ)≤L := by
    have hmono := Nat.log_mono_right (b := 2) hellr
    exact (by exact_mod_cast hmono : (Nat.log 2 ell : ℝ)≤Nat.log 2 (Nat.card X)).trans
      (Real.natLog_le_logb (Nat.card X) 2)
  have hsq : (((Nat.log 2 ell+2 : ℕ) : ℝ))^2≤9*L^2 := by
    push_cast
    have hnon : (0 : ℝ)≤Nat.log 2 ell := Nat.cast_nonneg _
    nlinarith
  have hcard := hA D ell hell
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by exact_mod_cast Nat.card_pos (α := D.Simple ≃* D.Simple) :
      (0 : ℝ)<Nat.card (D.Simple ≃* D.Simple))
    (show (Nat.card (D.Simple ≃* D.Simple) : ℝ)≤
      (Nat.card D.Simple : ℝ)^(A*(Nat.log 2 ell+2)^2) by exact_mod_cast hcard)
  rw [Real.logb_pow] at hlog
  have hs := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg A)
  have hprod := mul_le_mul hs hT hT0 (by positivity : (0 : ℝ)≤(A : ℝ)*(9*L^2))
  push_cast at hprod hlog
  dsimp [L] at *
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.card X)) (pow_nonneg hL0 3)]

end SymmetricSubgroupAsymptotics.CFSGActualSimpleAutomorphismLogBudget
