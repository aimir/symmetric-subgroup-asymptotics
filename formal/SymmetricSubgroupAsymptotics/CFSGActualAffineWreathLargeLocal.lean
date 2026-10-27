import SymmetricSubgroupAsymptotics.ActualAffineWreathWholeCount
import SymmetricSubgroupAsymptotics.CFSGWeakTransitiveGeneratorBound
import SymmetricSubgroupAsymptotics.LMMAffineWreathEnvelopeNumerics

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGActualAffineWreathLargeLocal

theorem uniform_large_local (hCFSG : CFSG.CFSGClassification) (ε : ℝ) (hε : 0<ε) :
    ∃ R0 : ℕ, ∀ {R X : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
      [FaithfulSMul R X] (P : PrimitiveAffineProfile R X) (x : X),
      R0≤Nat.card X → 2≤Nat.card X →
      ∀ t : ℕ, 2≤t → ∀ Q : Subgroup (Equiv.Perm (Fin t)),
        MulAction.IsPretransitive Q (Fin t) →
        (Nat.card (ActualFullWreathFamily.Family R Q (Fin t)) : ℝ)≤
          (2 : ℝ)^(ε*((Nat.card X*t : ℕ) : ℝ)^2) := by
  obtain ⟨C,hC,htop⟩ := CFSGWeakTransitiveGeneratorBound.exists_uniform_generator_budget hCFSG
  obtain ⟨R0,hscalar⟩ := LMMAffineWreathEnvelopeNumerics.affineCount_large_local
    4 C (by norm_num) (by linarith) ε hε
  refine ⟨R0,?_⟩
  intro R X _ _ _ _ _ P x hlarge hr t ht Q hQ
  let a := (Nat.log 2 (Nat.card X)+1)^2
  have hL : 1≤Real.logb 2 (Nat.card X : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (by norm_num : (0 : ℝ)<2) (by exact_mod_cast hr : (2 : ℝ)≤Nat.card X)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
  have ha : (a : ℝ)≤4*(Real.logb 2 (Nat.card X : ℝ))^2 := by
    have hh : (Nat.log 2 (Nat.card X) : ℝ)≤Real.logb 2 (Nat.card X : ℝ) := by
      simpa only [Nat.cast_ofNat] using Real.natLog_le_logb (Nat.card X) 2
    dsimp only [a]
    push_cast
    have hz : (0 : ℝ)≤Nat.log 2 (Nat.card X) := Nat.cast_nonneg _
    have hplus : (Nat.log 2 (Nat.card X) : ℝ)+1≤2*Real.logb 2 (Nat.card X : ℝ) := by linarith
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(Nat.log 2 (Nat.card X) : ℝ)+1) hplus 2
    nlinarith only [hs]
  have hslog : Real.logb 2 (Nat.card R : ℝ)≤a := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
      (by exact_mod_cast Nat.card_pos (α := R) : (0 : ℝ)<Nat.card R)
      (show (Nat.card R : ℝ)≤(2 : ℝ)^a by
        exact_mod_cast PrimitiveAffineUniformLocalCharge.card_le_binary_log_square P x)
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] using hh
  have hh := hscalar (Nat.card X) t a (MarkedC4.genRank Q) (Nat.card R)
    hlarge hr ht (Nat.card_pos) ha hslog (by simpa only [mul_div_assoc] using htop t ht Q hQ)
  have hc : Nat.card (ActualFullWreathFamily.Family R Q (Fin t))≤
      LMMAffineWreathEnvelopeNumerics.affineCount t a (MarkedC4.genRank Q) (Nat.card R) := by
    simpa only [a,Nat.card_fin,LMMAffineWreathEnvelopeNumerics.affineCount,pow_two] using
      ActualAffineWreathWholeCount.card_family_le (Q := Q) (I := Fin t) P x
  have hcR : (Nat.card (ActualFullWreathFamily.Family R Q (Fin t)) : ℝ)≤
      (LMMAffineWreathEnvelopeNumerics.affineCount t a (MarkedC4.genRank Q) (Nat.card R) : ℝ) := by
    exact_mod_cast hc
  exact hcR.trans hh

end SymmetricSubgroupAsymptotics.CFSGActualAffineWreathLargeLocal
