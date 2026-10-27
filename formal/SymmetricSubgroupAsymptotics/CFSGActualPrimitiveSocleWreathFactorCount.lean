import SymmetricSubgroupAsymptotics.ActualPrimitiveSocleWreathWholeCount
import SymmetricSubgroupAsymptotics.CFSGPrimitiveSocleQuotientFactorLogBudget
import SymmetricSubgroupAsymptotics.CFSGWeakTransitiveGeneratorBound

/-! CFSG-only actual primitive-local whole-family envelope with closed
binary local-quotient exponent and genuine transitive top rank. Numerical
absorption into a two-scale recurrence is a separate analytic step. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGActualPrimitiveSocleWreathFactorCount
open PrimitiveSocleRawStructure

theorem exists_uniform_envelope (hCFSG : CFSG.CFSGClassification) :
    ∃ B : ℕ, 1≤B ∧ ∃ C : ℝ, 1≤C ∧
      ∀ {R X : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
        (D : NonaffineData R X) (t : ℕ) (ht : 2≤t)
        (Q : Subgroup (Equiv.Perm (Fin t))) (hQ : MulAction.IsPretransitive Q (Fin t)),
      let a := Nat.log 2 (Nat.card (R ⧸ finiteGroupSocle R))+1
      let q := MarkedC4.genRank Q
      (a : ℝ)≤(B : ℝ)*D.factorCount*Real.logb 2 (Nat.card X : ℝ) ∧
      (q : ℝ)≤C*((t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))) ∧
      Nat.card (ActualFullWreathFamily.Family R Q (Fin t))≤
        (2^((t*a)*(t*a))*Nat.card (R ⧸ finiteGroupSocle R)^(t*q))*
        ((2^(t*D.factorCount)*
          (2*(1+(t*D.factorCount)*Nat.card (D.Simple ≃* D.Simple)))^(t*D.factorCount))*
          Nat.card D.Simple^((t*D.factorCount)*(t*a+q))) := by
  obtain ⟨B,hB,hlocal⟩ := CFSGPrimitiveSocleQuotientFactorLogBudget.exists_uniform_budget hCFSG
  obtain ⟨C,hC,htop⟩ := CFSGWeakTransitiveGeneratorBound.exists_uniform_generator_budget hCFSG
  refine ⟨B,hB,C,hC,?_⟩
  intro R X _ _ _ _ D t ht Q hQ
  dsimp only
  refine ⟨?_,htop t ht Q hQ,?_⟩
  · exact hlocal D
  · obtain ⟨f,hf⟩ := ActualFullWreathSemisimpleWholeCount.exists_tuple
      (MarkedC4.genRank Q) (le_refl _)
    have ha : Nat.card (R ⧸ finiteGroupSocle R)≤
        2^(Nat.log 2 (Nat.card (R ⧸ finiteGroupSocle R))+1) :=
      (Nat.lt_pow_succ_log_self (by decide : 1<2) _).le
    have hh := ActualPrimitiveSocleWreathWholeCount.card_family_le (Q := Q) (I := Fin t) D _ ha f hf
    simpa only [Nat.card_fin] using hh

end SymmetricSubgroupAsymptotics.CFSGActualPrimitiveSocleWreathFactorCount
