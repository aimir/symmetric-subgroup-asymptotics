import SymmetricSubgroupAsymptotics.PrimeDerivedProperIntersection
import Lean.Elab.Tactic.Omega

/-! A normal subgroup crossing the original derived subgroup determines
a one-dimensional space of whole-group invariant derived characters
vanishing on its intersection, whenever actual independent form pairs
have zero common radical. No quotient-center or double-annihilator
identification is used here. In characteristic two the nonzero original
character itself is unique, not merely its scalar line. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G]

section Prime

variable (p : ℕ) [Fact p.Prime]
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (hG : IsPGroup p G)
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters p (commutator G),
      LinearIndependent (ZMod p) v →
      (derivedEvaluationBilinearMap p hker (v 0)).ker ⊓
        (derivedEvaluationBilinearMap p hker (v 1)).ker = ⊥)

include hker hG hpair

/-- Proper intersection supplies a nonzero original character, while a
second independent one would force N inside the actual derived group. -/
theorem derivedCharactersVanishingOn_finrank_eq_one_of_crossing
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N) :
    Module.finrank (ZMod p)
      (derivedCharactersVanishingOn p (N ⊓ commutator G)) = 1 := by
  have hone := derivedCharactersVanishingOn_one_le_of_lt p hG
    (N ⊓ commutator G) (derivedIntersection_lt_of_not_derived_le N hnotDN)
  have hnotTwo : ¬2 ≤ Module.finrank (ZMod p)
      (derivedCharactersVanishingOn p (N ⊓ commutator G)) := by
    intro htwo
    exact hnotND (derivedCharactersVanishingOn_normal_le_commutator_of_two_le
      p hker hpair (N ⊓ commutator G) N le_rfl htwo)
  omega

/-- Every nonzero member spans this same literal character subspace. -/
theorem derivedCharactersVanishingOn_eq_span_of_crossing
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N)
    (χ : primeRelativeCharacters p (commutator G))
    (hχ : χ ∈ derivedCharactersVanishingOn p (N ⊓ commutator G)) (hχ0 : χ ≠ 0) :
    derivedCharactersVanishingOn p (N ⊓ commutator G) =
      Submodule.span (ZMod p) {χ} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem χ _).mpr hχ)
  rw [finrank_span_singleton hχ0,
    derivedCharactersVanishingOn_finrank_eq_one_of_crossing p hker hG hpair N hnotND hnotDN]

/-- The spanning character is an actual invariant character on G',
obtained from an original normal index-p interval above N∩G'. -/
theorem exists_derivedCharacter_spanning_of_crossing
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N) :
    ∃ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 ∧
      derivedCharactersVanishingOn p (N ⊓ commutator G) =
        Submodule.span (ZMod p) {χ} := by
  obtain ⟨χ, hχ0, hχ⟩ := pGroup_exists_nonzero_derivedCharacter_vanishing hG
    (N ⊓ commutator G) (derivedIntersection_lt_of_not_derived_le N hnotDN)
  exact ⟨χ, hχ0, derivedCharactersVanishingOn_eq_span_of_crossing
    p hker hG hpair N hnotND hnotDN χ hχ hχ0⟩

end Prime

/-- In a binary group the character itself, rather than only its line,
is uniquely specified by the actual crossing normal intersection. -/
theorem binaryDerivedCrossing_exists_unique_nonzero
    (hker : (primeAbelianizationGroupMap 2 G).ker = commutator G)
    (hG : IsPGroup 2 G)
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters 2 (commutator G),
      LinearIndependent (ZMod 2) v →
      (derivedEvaluationBilinearMap 2 hker (v 0)).ker ⊓
        (derivedEvaluationBilinearMap 2 hker (v 1)).ker = ⊥)
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N) :
    ∃! χ : primeRelativeCharacters 2 (commutator G),
      χ ∈ derivedCharactersVanishingOn 2 (N ⊓ commutator G) ∧ χ ≠ 0 := by
  obtain ⟨χ, hχ0, hspan⟩ := exists_derivedCharacter_spanning_of_crossing
    2 hker hG hpair N hnotND hnotDN
  refine ⟨χ, ⟨?_, hχ0⟩, ?_⟩
  · rw [hspan]
    exact Submodule.mem_span_singleton_self χ
  · intro ψ hψ
    have hm : ψ ∈ Submodule.span (ZMod 2) {χ} := by
      rw [← hspan]
      exact hψ.1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have hscalar : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    rcases hscalar c with rfl | rfl
    · exact False.elim (hψ.2 (by simpa only [zero_smul] using hc.symm))
    · simpa only [one_smul] using hc.symm

end SymmetricSubgroupAsymptotics
