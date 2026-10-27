import SymmetricSubgroupAsymptotics.FiniteModelOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.NonabelianSimpleOrderAtLeastSixty
import SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
import SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics

/-! All-factor finite-model primitive ordinary budgets from raw degree
geometry. No smaller transitive induction, index-square, outer numerical
callback, model order, or generating-pair hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget
open PrimitiveSocleRawStructure CFSGReduction
open FiniteModelOneFactorOrdinaryTail

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem two_pow_factorCount_le_degree (D : NonaffineData G X) :
    2^D.factorCount ≤ Nat.card X := by
  rcases D.indexForm with ⟨H,hH,he⟩ | ⟨a,hka,he⟩
  · rw [he]
    exact Nat.pow_le_pow_left (by have h := H.one_lt_index_of_ne_top hH; omega) _
  · have hfour : 4 ≤ Nat.card D.Simple := by
      have hh := NonabelianSimpleOrderAtLeastSixty.sixty_le_card D.Simple D.noncommutative
      omega
    rw [he]
    calc
      2^D.factorCount ≤ 2^(2*a) := Nat.pow_le_pow_right (by decide) hka
      _ = 4^a := by rw [pow_mul]; norm_num
      _ ≤ (Nat.card D.Simple)^a := Nat.pow_le_pow_left hfour a

theorem factorCount_le_log (D : NonaffineData G X) :
    D.factorCount ≤ Nat.log 2 (Nat.card X) :=
  Nat.le_log_of_pow_le (by decide) (two_pow_factorCount_le_degree D)

theorem factorial_cardFactors_le_square (k : ℕ) :
    ArithmeticFunction.cardFactors k.factorial ≤ k^2 := by
  have hh := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    k.factorial (Nat.factorial_pos k).ne').trans
    (CFSGCoarsePrimitiveNumerics.factorial_logb_le_square k)
  exact_mod_cast hh

variable [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

theorem genRank_le_model_budget {M : Type} [Group M] [Finite M]
    (D : NonaffineData G X) (e : D.Simple ≃* M) :
    MarkedC4.genRank G ≤
      (Nat.log 2 (Nat.card X)+2)*modelCost M+(Nat.log 2 (Nat.card X))^2 := by
  have hbase := PrimitiveSocleIsotypicOrdinaryCompression.genRank_le_twice_simple_add_quotient D
  have hquot := PrimitiveSocleStrictOuterOrdinaryRecurrence.quotient_genRank_le_outer_multiplicity D
  have hrank : MarkedC4.genRank D.Simple=MarkedC4.genRank M :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv e
  have hout : ArithmeticFunction.cardFactors (Nat.card (Outer D.Simple))=
      ArithmeticFunction.cardFactors (Nat.card (Outer M)) := congrArg _ (outer_card_congr e)
  rw [hrank] at hbase
  rw [hout] at hquot
  have hk := factorCount_le_log D
  have hfact := (factorial_cardFactors_le_square D.factorCount).trans
    (Nat.pow_le_pow_left hk 2)
  have hs : MarkedC4.genRank M ≤ modelCost M := Nat.le_add_right _ _
  have ho : ArithmeticFunction.cardFactors (Nat.card (Outer M)) ≤ modelCost M := Nat.le_add_left _ _
  have hfirst : 2*MarkedC4.genRank M ≤ 2*modelCost M := Nat.mul_le_mul_left _ hs
  have hsecond : D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer M)) ≤
      Nat.log 2 (Nat.card X)*modelCost M := Nat.mul_le_mul hk ho
  calc
    MarkedC4.genRank G ≤ 2*MarkedC4.genRank M+
        (D.factorCount*ArithmeticFunction.cardFactors (Nat.card (Outer M))+
          ArithmeticFunction.cardFactors D.factorCount.factorial) :=
      hbase.trans (Nat.add_le_add_left hquot _)
    _ ≤ 2*modelCost M+(Nat.log 2 (Nat.card X)*modelCost M+
        (Nat.log 2 (Nat.card X))^2) :=
      Nat.add_le_add hfirst (Nat.add_le_add hsecond hfact)
    _ = _ := by ring

/-- Uniform budget on the SAME data/e, including all factor counts. -/
def HasModelBudget (M : Type) [Group M] (C : ℕ) : Prop :=
  ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X), (D.Simple ≃* M) →
      MarkedC4.genRank G ≤ (Nat.log 2 (Nat.card X)+2)*C+(Nat.log 2 (Nat.card X))^2

theorem exists_model_budget (M : Type) [Group M] : ∃ C, HasModelBudget M C := by
  by_cases h : Finite M
  · letI := h
    refine ⟨modelCost M,?_⟩
    intro G X _ _ _ _ _ _ _ D e
    exact genRank_le_model_budget D e
  · refine ⟨0,?_⟩
    intro G X _ _ _ _ _ _ _ D e
    exact (h (Finite.of_equiv D.Simple e.toEquiv)).elim

theorem model_budget_mono {M : Type} [Group M] {C C' : ℕ}
    (h : HasModelBudget M C) (hCC : C ≤ C') : HasModelBudget M C' := by
  intro G X _ _ _ _ _ _ _ D e
  exact (h D e).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hCC) _)

theorem finite_family_budget {ι : Type} [Finite ι]
    (M : ι → Type) [∀ i,Group (M i)] :
    ∃ C, ∀ i, HasModelBudget (M i) C := by
  letI := Fintype.ofFinite ι
  choose C hC using fun i => exists_model_budget (M i)
  exact ⟨Finset.univ.sup C,fun i => model_budget_mono (hC i) (Finset.le_sup (Finset.mem_univ i))⟩

end SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget
