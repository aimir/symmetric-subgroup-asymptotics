import SymmetricSubgroupAsymptotics.CFSGCatalogueWithAxiomMonster
import SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443FiniteBudgets
import SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitivePolylogRank

/-! The genuine finite-menu absorption needed by the direct-classifier
LMM chain. Every old non-M infinite family uses its existing literal model
packet. Raw Y443 is one additional fixed finite-menu entry; its source need
not be known finite globally. Finiteness is inherited only from actual e.
No numerical callback, exact Tracey input or old classification is used.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ExtendedCatalogueNonaffinePrimitiveRank
open PrimitiveSocleRawStructure CFSGReduction CFSGNonaffinePrimitivePolylogRank
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction (RemainingModel)
open FiniteModelPrimitiveOrdinaryBudget

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

private theorem finite_model_bound (C : ℕ)
    (hC : ∀ j,HasModelBudget (CFSGAxiomMonsterY443FiniteBudgets.finiteModel j) C)
    (j : CFSG.Index) (hj : RemainingModel j) (e : D.Simple ≃* j.Model) :
    MarkedC4.genRank G≤(Nat.log 2 (Nat.card X)+2)*C+(Nat.log 2 (Nat.card X))^2 := by
  cases j <;> try { exact hj.elim }
  case tits => exact hC (some none) D e
  case sporadic s => exact hC (some (some s)) D e

/-- Internal uniform rank budget on actual primitive sources. -/
theorem exists_uniform_rank_budget (hclass : CFSGCatalogueWithAxiomMonster.Classification) :
    ∃ A : ℕ, ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
      [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
      (D : NonaffineData G X),
      MarkedC4.genRank G≤A*(Nat.log 2 (Nat.card X)+2)^2 := by
  obtain ⟨C,hC⟩ := CFSGAxiomMonsterY443FiniteBudgets.exists_uniform_primitive_finite_menu_budget
  refine ⟨C+32,?_⟩
  intro G X _ _ _ _ _ _ _ D
  let l := Nat.log 2 (Nat.card X)
  have hbranch :
      (MarkedC4.genRank G : ℝ)≤25*(Real.logb 2 (Nat.card X : ℝ))^2+
        4*Real.logb 2 (Nat.card X : ℝ)+2 ∨
      MarkedC4.genRank G≤(l+2)*C+l^2 := by
    obtain ⟨i,e⟩ := CFSGCatalogueWithAxiomMonster.modelWitness hclass D.Simple
    cases i with
    | inr u => exact Or.inr (hC none D e)
    | inl i =>
      let e0 : D.Simple ≃* i.val.Model := e
      letI : Finite i.val.Model := Finite.of_equiv D.Simple e0.toEquiv
      letI : IsSimpleGroup i.val.Model := e0.symm.isSimpleGroup
      have hn : ¬IsMulCommutative i.val.Model :=
        fun hc => D.noncommutative ((isMulCommutative_congr e0).mpr hc)
      obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
      rcases CFSGInfiniteSimplePolylogRank.simple_rank_or_remaining D i.val e0 ell hell with hr | hi
      · rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining i.val hn with hp | hi
        · obtain ⟨ho,ha⟩ := sufficientSimpleIndexBounds_of_mulEquiv e0 hp ell hell
          exact Or.inl (PrimitiveSimplePolylogRankTools.primitive_rank_le_of_simple_packet D ell hell ho ha hr)
        · exact Or.inr (finite_model_bound D C hC i.val hi e0)
      · exact Or.inr (finite_model_bound D C hC i.val hi e0)
  rcases hbranch with hr | hb
  · have hu := logb_le_natLog_add_one (Nat.card X) (Nat.card_pos)
    have h2 : 2≤Nat.card X := by
      have hh : 1<Nat.card X := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    have hL : 1≤Real.logb 2 (Nat.card X : ℝ) := by
      have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
        (by norm_num : (0 : ℝ)<2) (by exact_mod_cast h2 : (2 : ℝ)≤Nat.card X)
      simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] using hh
    have hl0 : (0 : ℝ)≤l := by positivity
    have hc0 : (0 : ℝ)≤C := by positivity
    have hs : (Real.logb 2 (Nat.card X : ℝ))^2≤((l : ℝ)+1)^2 :=
      (sq_le_sq₀ (by linarith) (by positivity)).mpr hu
    have hh : (MarkedC4.genRank G : ℝ)≤((C+32 : ℕ) : ℝ)*((l+2 : ℕ) : ℝ)^2 := by
      push_cast
      nlinarith only [hr,hu,hL,hs,hl0,hc0,
        mul_nonneg hc0 (sq_nonneg ((l : ℝ)+2))]
    exact_mod_cast hh
  · have hb' : (l+2)*C+l^2≤(C+32)*(l+2)^2 := by
      nlinarith only [Nat.zero_le C,Nat.zero_le l,Nat.zero_le (C*l*l),Nat.zero_le (C*l)]
    exact hb.trans hb'

end SymmetricSubgroupAsymptotics.ExtendedCatalogueNonaffinePrimitiveRank
