import SymmetricSubgroupAsymptotics.CFSGActualPrimitiveSocleWreathFactorCount
import SymmetricSubgroupAsymptotics.CFSGActualSimpleAutomorphismLogBudget
import SymmetricSubgroupAsymptotics.LMMPrimitiveSocleWreathEnvelopeNumerics

/-! Actual nonaffine primitive-local families are uniformly subquadratic
as the LOCAL degree grows, at every top degree. Every arithmetic premise
of the scalar envelope is discharged using the SAME actual D. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGActualNonaffineWreathLargeLocal
open PrimitiveSocleRawStructure

theorem uniform_large_local (hCFSG : CFSG.CFSGClassification) (ε : ℝ) (hε : 0<ε) :
    ∃ R0 : ℕ, ∀ {R X : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
      [FaithfulSMul R X] (D : NonaffineData R X), R0≤Nat.card X → 2≤Nat.card X →
      ∀ t : ℕ, 2≤t → ∀ Q : Subgroup (Equiv.Perm (Fin t)),
        MulAction.IsPretransitive Q (Fin t) →
        (Nat.card (ActualFullWreathFamily.Family R Q (Fin t)) : ℝ)≤
          (2 : ℝ)^(ε*((Nat.card X*t : ℕ) : ℝ)^2) := by
  obtain ⟨B,hB,C,hC,hfamily⟩ := CFSGActualPrimitiveSocleWreathFactorCount.exists_uniform_envelope hCFSG
  obtain ⟨A,hA,hauto⟩ := CFSGActualSimpleAutomorphismLogBudget.exists_uniform_budget hCFSG
  obtain ⟨R0,hscalar⟩ := LMMPrimitiveSocleWreathEnvelopeNumerics.wholeCount_large_local
    (A : ℝ) (B : ℝ) C (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith) ε hε
  refine ⟨R0,?_⟩
  intro R X _ _ _ _ _ D hlarge hr t ht Q hQ
  obtain ⟨ha,hq,hcount⟩ := hfamily D t ht Q hQ
  have hT0 : 0≤Real.logb 2 (Nat.card D.Simple : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (Nat.card_pos (α := D.Simple)))
  have hk1 : (1 : ℝ)≤D.factorCount := by
    exact_mod_cast (show 1≤D.factorCount by have hh := D.factorCount_pos; omega)
  have hblog : Real.logb 2 (Nat.card D.Simple : ℝ)≤
      (Nat.card X : ℝ)*Real.logb 2 (Nat.card X : ℝ) :=
    (le_mul_of_one_le_left hT0 hk1).trans (ActualPrimitiveSocleLogSizeBounds.socle_log_le D hr)
  have hslog := CFSGNonaffinePrimitivePolylogRank.logb_le_natLog_add_one
    (Nat.card (R ⧸ finiteGroupSocle R)) (Nat.card_pos)
  have hh := hscalar (Nat.card X) t D.factorCount
    (Nat.log 2 (Nat.card (R ⧸ finiteGroupSocle R))+1) (MarkedC4.genRank Q)
    (Nat.card (R ⧸ finiteGroupSocle R)) (Nat.card D.Simple)
    (Nat.card (D.Simple ≃* D.Simple)) hlarge hr ht
    (Nat.card_pos) (Nat.card_pos) (Nat.card_pos)
    (ActualPrimitiveSocleLogSizeBounds.factorCount_le_log D) ha
    (by simpa only [Nat.cast_add,Nat.cast_one] using hslog) hblog (hauto D hr)
    (by simpa only [mul_div_assoc] using hq)
  have hc : Nat.card (ActualFullWreathFamily.Family R Q (Fin t))≤
      LMMPrimitiveSocleWreathEnvelopeNumerics.wholeCount t D.factorCount
        (Nat.log 2 (Nat.card (R ⧸ finiteGroupSocle R))+1) (MarkedC4.genRank Q)
        (Nat.card (R ⧸ finiteGroupSocle R)) (Nat.card D.Simple)
        (Nat.card (D.Simple ≃* D.Simple)) := by
    simpa only [LMMPrimitiveSocleWreathEnvelopeNumerics.wholeCount,
      LMMHomogeneousSupportNumerics.supportCount,pow_two] using hcount
  have hcR : (Nat.card (ActualFullWreathFamily.Family R Q (Fin t)) : ℝ)≤
      (LMMPrimitiveSocleWreathEnvelopeNumerics.wholeCount t D.factorCount
        (Nat.log 2 (Nat.card (R ⧸ finiteGroupSocle R))+1) (MarkedC4.genRank Q)
        (Nat.card (R ⧸ finiteGroupSocle R)) (Nat.card D.Simple)
        (Nat.card (D.Simple ≃* D.Simple)) : ℝ) := by exact_mod_cast hc
  exact hcR.trans hh

end SymmetricSubgroupAsymptotics.CFSGActualNonaffineWreathLargeLocal
