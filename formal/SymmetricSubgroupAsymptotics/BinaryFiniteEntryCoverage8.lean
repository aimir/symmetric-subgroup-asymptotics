import SymmetricSubgroupAsymptotics.BinaryNormalCoverage8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T1
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T2
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T3
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T4
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T5
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T6
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T7
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T8
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T9
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T10
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T11
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T15
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T16
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T17
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T19
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T20
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T21
import SymmetricSubgroupAsymptotics.GeneratedPair8.Entry8T30

/-! Complete finite-entry coverage in width eight. All 203 nonbase normal
records are installed; the eight existing base action indices stay explicit.
This is not an analytic character-owner or global weighted-sum theorem. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryFiniteEntryCoverage8
open BinaryNormalCoverage8 BinaryActionRegistry8
open scoped Pointwise

theorem finiteEntryCoverage (i : Fin 26) (hi : i∉baseIndices)
    (N : Subgroup (actions i)) [hN : N.Normal] : BinaryFiniteEntry8 (actions i) N := by
  fin_cases i
  · exact @BinaryFiniteEntry8T1.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T2.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T3.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T4.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T5.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T6.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T7.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T8.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T9.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T10.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T11.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T15.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T16.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T17.finiteEntryCoverage N hN
  · exact False.elim (hi (by decide +kernel))
  · exact @BinaryFiniteEntry8T19.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T20.finiteEntryCoverage N hN
  · exact @BinaryFiniteEntry8T21.finiteEntryCoverage N hN
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))
  · exact @BinaryFiniteEntry8T30.finiteEntryCoverage N hN
  · exact False.elim (hi (by decide +kernel))
  · exact False.elim (hi (by decide +kernel))

/-- One original ambient conjugation preserves the specified normal and
original normalizer while placing it in its checked finite branch. -/
theorem complete (H : Subgroup (Equiv.Perm (Fin 8))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) (N : Subgroup H) [N.Normal] :
    ∃ i : Fin 26, ∃ g : Equiv.Perm (Fin 8), ∃ hg : MulAut.conj g • H=actions i,
      (i∈baseIndices ∨ BinaryFiniteEntry8 (actions i) (actionConjugacyNormal g hg N)) ∧
      Nat.card (Subgroup.normalizer (H:Set (Equiv.Perm (Fin 8))))=
        Nat.card (Subgroup.normalizer (actions i:Set (Equiv.Perm (Fin 8)))) := by
  obtain ⟨i,g,hg⟩ := BinaryActionRegistry8.complete H hH ht
  refine ⟨i,g,hg,?_,actionConjugacy_normalizer_card g hg⟩
  by_cases hi : i∈baseIndices
  · exact Or.inl hi
  · exact Or.inr (finiteEntryCoverage i hi (actionConjugacyNormal g hg N))
end SymmetricSubgroupAsymptotics.BinaryFiniteEntryCoverage8
