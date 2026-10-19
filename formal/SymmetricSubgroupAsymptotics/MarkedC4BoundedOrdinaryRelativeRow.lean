import SymmetricSubgroupAsymptotics.MarkedC4PublishedOrdinaryNilpotentGeneration

/-! Concrete fixed-cutoff relative rows from ordinary published group theory.
The SAME boundedNilpotentCount family is passed to the physical product
construction. Actual cores, tuples, recovery and Hom weights are constructed
by OrbitCutoffFamilies.relativeRow, not postulated as literature input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.BoundedOrdinaryRelativeRow
open OrdinaryNilpotentGeneration

def tupleLength (C b : ℕ) : ℕ :=
  ⌈4*(C.factorial : ℝ)*Real.sqrt (2*b : ℕ)⌉₊

/-- The full physical symmetric alphabet is deliberately used; this avoids
any extra container-selection premise. Its logarithm is O_C(√b b log b). -/
def tupleCost (C b : ℕ) : ℝ :=
  Real.logb 2 (Fintype.card (⊤ : Subgroup (PermutationGroup b)) : ℝ)*tupleLength C b

theorem alphabet_bound (C b : ℕ) :
    (Fintype.card (⊤ : Subgroup (PermutationGroup b)) : ℝ)^tupleLength C b ≤
      (2 : ℝ)^tupleCost C b := by
  unfold tupleCost
  rw [Real.rpow_mul (by norm_num : (0 : ℝ)≤2),
    Real.rpow_logb (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)
      (by positivity),Real.rpow_natCast]

/-- No abstract ordinary-generation hypothesis remains at the row level:
its sole group-theory inputs are the named ordinary Theorem7, Lemma8.5,
and pre-existing Kovács--Praeger bound. -/
def relativeRow
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (hKP : KovacsPraegerAbelianizationBound) (C b : ℕ) :
    RelativeGeneratorEncodingRow
      (OrbitCutoffFamilies.solubleCount C) (OrbitCutoffFamilies.nilpotentCount C)
      (tupleCost C) (tupleLength C b) b := by
  apply OrbitCutoffFamilies.relativeRow C b (tupleLength C b) ?_
    (tupleCost C) (alphabet_bound C b)
  intro G
  letI : IsSolvable G.1 := G.2.1
  obtain ⟨K,S,hnil,hcard,hgen⟩ :=
    bounded_nilpotent_generation hsub hseven hKP G.1 G.2.2
  refine ⟨K,S,hnil,?_,hgen⟩
  have hceil : (S.card : ℝ) ≤ (tupleLength C b : ℝ) :=
    hcard.trans (Nat.le_ceil _)
  exact_mod_cast hceil

end SymmetricSubgroupAsymptotics.MarkedC4.BoundedOrdinaryRelativeRow
