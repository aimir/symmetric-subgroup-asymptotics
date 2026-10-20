import SymmetricSubgroupAsymptotics.BoundedOrbitNilpotentCoreGeneration
import SymmetricSubgroupAsymptotics.MarkedC4BoundedOrdinaryRelativeNumerics

/-! The original physical cutoff and nilpotent family are retained. Only
the tuple-length constant is enlarged, so the existing sublinear and
subquadratic estimates apply unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.BoundedNilpotentCoreRelativeReduction
open OrdinaryNilpotentGeneration

abbrev tupleLength (C b : ℕ) :=
  BoundedOrdinaryRelativeRow.tupleLength (nilpotentControlCutoff C) b
abbrev tupleCost (C b : ℕ) :=
  BoundedOrdinaryRelativeRow.tupleCost (nilpotentControlCutoff C) b

def relativeRow (hKP : KovacsPraegerAbelianizationBound) (C b : ℕ) :
    RelativeGeneratorEncodingRow
      (OrbitCutoffFamilies.solubleCount C) (OrbitCutoffFamilies.nilpotentCount C)
      (tupleCost C) (tupleLength C b) b := by
  apply OrbitCutoffFamilies.relativeRow C b (tupleLength C b) ?_
    (tupleCost C) (BoundedOrdinaryRelativeRow.alphabet_bound (nilpotentControlCutoff C) b)
  intro G
  letI : IsSolvable G.1 := G.2.1
  obtain ⟨K,S,hK,hS,hgen⟩ := bounded_orbit_nilpotent_core_generation_real hKP G.1 G.2.2
  refine ⟨K,S,hK,?_,hgen⟩
  have hceil : (S.card : ℝ)≤(tupleLength C b : ℝ) := hS.trans (Nat.le_ceil _)
  exact_mod_cast hceil

def reduction (hKP : KovacsPraegerAbelianizationBound) (C : ℕ) :
    PublishedRelativeGeneratorReduction
      (OrbitCutoffFamilies.solubleCount C) (OrbitCutoffFamilies.nilpotentCount C) where
  q := tupleCost C
  l := tupleLength C
  q_subquadratic := BoundedOrdinaryRelativeRow.tupleCost_subquadratic (nilpotentControlCutoff C)
  l_sublinear := BoundedOrdinaryRelativeRow.tupleLength_sublinear (nilpotentControlCutoff C)
  row := relativeRow hKP C

end SymmetricSubgroupAsymptotics.MarkedC4.BoundedNilpotentCoreRelativeReduction
