import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.LinearLogOrdinaryGeneratorTail
import Mathlib.Data.Finset.Lattice.Fold

/-! An actual fixed finite simple model pays the exact primitive coarse
ceiling eventually, without a displayed pair or known order. The model
need not have a global Finite instance: an actual equivalence supplies it.
This is only a one-factor tail, not the all-degree transitive input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteModelOneFactorOrdinaryTail
open PrimitiveSocleRawStructure CFSGReduction

theorem constant_le_ceiling (K n : ℕ) (hn : 128 ≤ n) (hpow : 2^K ≤ n) :
    K ≤ traceyPermutationGeneratorCeiling n := by
  have hlog : (K : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ)^K)
      (by exact_mod_cast hpow : (2 : ℝ)^K ≤ (n : ℝ))
    simpa only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] using hh
  have hlinear : (K : ℝ) ≤ 5*Real.logb 2 (n : ℝ)+3 := by
    have hk : (0 : ℝ) ≤ K := by positivity
    linarith only [hlog,hk]
  have hh := hlinear.trans ((LinearLogOrdinaryGeneratorTail.aggregate_le n hn).trans
    (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)))))
  change (K : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

def modelCost (M : Type) [Group M] [Finite M] : ℕ :=
  MarkedC4.genRank M+ArithmeticFunction.cardFactors (Nat.card (Outer M))

theorem genRank_le_modelCost
    {G X M : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [Group M] [Finite M] (D : NonaffineData G X)
    (hk : D.factorCount=1) (e : D.Simple ≃* M) :
    MarkedC4.genRank G ≤ modelCost M := by
  have hh := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  simpa only [modelCost,CoprimeNilpotentProductGenerators.genRank_mulEquiv e,
    outer_card_congr e] using hh

/-- The exact same-D/e tail property; no actual model-generation hypothesis. -/
def PaysOneFactorModel (M : Type) [Group M] (N : ℕ) : Prop :=
  ∀ {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X), D.factorCount=1 → (D.Simple ≃* M) →
      N ≤ Nat.card X →
      MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X)

theorem pays_of_finite (M : Type) [Group M] [Finite M] :
    PaysOneFactorModel M (max 128 (2^(modelCost M))) := by
  intro G X _ _ _ _ D hk e hn
  exact (genRank_le_modelCost D hk e).trans (constant_le_ceiling _ _
    ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn))

theorem pays_mono {M : Type} [Group M] {N N' : ℕ}
    (h : PaysOneFactorModel M N) (hNN : N ≤ N') : PaysOneFactorModel M N' := by
  intro G X _ _ _ _ D hk e hn
  exact h D hk e (hNN.trans hn)

/-- Unconditional: if a model is infinite, no finite actual simple factor
can be equivalent to it. No guessed model-finiteness theorem is used. -/
theorem exists_threshold (M : Type) [Group M] : ∃ N, PaysOneFactorModel M N := by
  by_cases h : Finite M
  · letI := h
    exact ⟨_,pays_of_finite M⟩
  · refine ⟨0,?_⟩
    intro G X _ _ _ _ D hk e hn
    exact (h (Finite.of_equiv D.Simple e.toEquiv)).elim

theorem finite_family_threshold {ι : Type} [Finite ι]
    (M : ι → Type) [∀ i,Group (M i)] :
    ∃ N, ∀ i, PaysOneFactorModel (M i) N := by
  letI := Fintype.ofFinite ι
  choose N hN using fun i => exists_threshold (M i)
  refine ⟨Finset.univ.sup N,?_⟩
  intro i
  exact pays_mono (hN i) (Finset.le_sup (Finset.mem_univ i))

end SymmetricSubgroupAsymptotics.FiniteModelOneFactorOrdinaryTail
