import SymmetricSubgroupAsymptotics.CFSGAlternatingOneOutsider
import SymmetricSubgroupAsymptotics.CFSGAlternatingCrossResidues
import SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossResidues
import SymmetricSubgroupAsymptotics.CFSGAlternatingFiveGoodSylow
import SymmetricSubgroupAsymptotics.CFSGConjugateSylowGenerationTransport
import Mathlib.Tactic.IntervalCases

/-! Uniform actual alternating two-conjugate Sylow generation, including
degrees six through eight. The four residue constructions are transported
by literal finite point bijections. Normalizer solubility remains separate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSylowGeneration
open CFSGAlternatingCyclicReflection CFSGAlternatingCrossSeed CFSGAlternatingCrossJoin
open CFSGConjugateSylowGenerationTransport

theorem relabel_sum (k r : ℕ)
    (h : ∃ P : Sylow 2 (Alt k r), join k r P = ⊤) :
    ∃ (P : Sylow 2 (alternatingGroup (Fin (4 * k + 1 + r))))
      (g : alternatingGroup (Fin (4 * k + 1 + r))),
      Subgroup.closure ((P : Set (alternatingGroup (Fin (4 * k + 1 + r)))) ∪
        (P : Subgroup (alternatingGroup (Fin (4 * k + 1 + r)))).map
          (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨P, hP⟩ := h
  apply exists_generating_conjugates_relabel (4 * k + 1 + r)
    (show Fintype.card (X k r) = 4 * k + 1 + r by
      rw [Fintype.card_sum, ZMod.card, Fintype.card_fin])
  exact ⟨P, rotationElement k r, hP⟩

theorem exists_generating_conjugates (n : ℕ) (hn : 5 ≤ n) :
    ∃ (P : Sylow 2 (alternatingGroup (Fin n))) (g : alternatingGroup (Fin n)),
      Subgroup.closure ((P : Set (alternatingGroup (Fin n))) ∪
        (P : Subgroup (alternatingGroup (Fin n))).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  by_cases hn5 : n = 5
  · subst n
    obtain ⟨_, P, g, _, hgen⟩ := CFSGAlternatingFiveGoodSylow.goodSylowPrime
    exact ⟨P, g, hgen⟩
  obtain ⟨k, r, hr, he⟩ : ∃ k r : ℕ, r < 4 ∧ n = 4 * k + 1 + r := by
    refine ⟨(n - 1) / 4, (n - 1) % 4, Nat.mod_lt _ (by decide), ?_⟩
    have h := Nat.mod_add_div (n - 1) 4
    omega
  have hk : 1 ≤ k := by omega
  subst n
  interval_cases r
  · by_cases hk2 : 2 ≤ k
    · obtain ⟨P, hP⟩ :=
        CFSGAlternatingCyclicSylowGeneration.exists_sylow_two_conjugates_generate k hk2
      apply exists_generating_conjugates_relabel (4 * k + 1 + 0)
        (show Fintype.card (Cycle k) = 4 * k + 1 + 0 by simp only [ZMod.card, Nat.add_zero])
      exact ⟨P, CFSGAlternatingCyclicSylowGeneration.rotationElement k, hP⟩
    · have hk1 : k = 1 := by omega
      subst k
      exact False.elim (hn5 rfl)
  · exact relabel_sum k 1 (CFSGAlternatingOneOutsider.exists_one_outsider_sylow_generation k hk)
  · by_cases hk2 : 2 ≤ k
    · exact relabel_sum k 2 (CFSGAlternatingCrossResidues.exists_two_outsider_sylow_generation k hk2)
    · have hk1 : k = 1 := by omega
      subst k
      exact relabel_sum 1 2 CFSGAlternatingSmallCrossResidues.degree_seven_sylow_generation
  · by_cases hk2 : 2 ≤ k
    · exact relabel_sum k 3 (CFSGAlternatingCrossResidues.exists_three_outsider_sylow_generation k hk2)
    · have hk1 : k = 1 := by omega
      subst k
      exact relabel_sum 1 3 CFSGAlternatingSmallCrossResidues.degree_eight_sylow_generation

end SymmetricSubgroupAsymptotics.CFSGAlternatingSylowGeneration
