import SymmetricSubgroupAsymptotics.PrimeDerivedCrossingCharacters
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterDetection

/-! A crossing original normal subgroup determines an actual derived
character kernel after adjoining the relative radical. The radical join
is removed only under a separately supplied containment. The character,
its kernel, the original derived subgroup and original ambient inclusion
are retained throughout. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (hG : IsPGroup p G)
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters p (commutator G),
      LinearIndependent (ZMod p) v →
      (derivedEvaluationBilinearMap p hker (v 0)).ker ⊓
        (derivedEvaluationBilinearMap p hker (v 1)).ker = ⊥)

include hker hG hpair

/-- Every nonzero original character in the crossing vanishing line
detects exactly the intersection joined with the actual relative radical. -/
theorem derivedCrossing_sup_radical_eq_mapped_character_ker
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N)
    (χ : primeRelativeCharacters p (commutator G))
    (hχ : χ ∈ derivedCharactersVanishingOn p (N ⊓ commutator G)) (hχ0 : χ ≠ 0) :
    (N ⊓ commutator G) ⊔ primeRelativeRadical p (commutator G) =
      (AddMonoidHom.toMultiplicativeRight χ.1).ker.map (commutator G).subtype := by
  have hspan := derivedCharactersVanishingOn_eq_span_of_crossing
    p hker hG hpair N hnotND hnotDN χ hχ hχ0
  change primeRelativeCharactersVanishingOn p (commutator G) (N ⊓ commutator G) =
    Submodule.span (ZMod p) {χ} at hspan
  exact sup_primeRelativeRadical_eq_mapped_character_ker_of_span
    p (commutator G) (N ⊓ commutator G) inf_le_right χ hspan

/-- The exact original intersection is the character kernel only when
the relative radical has separately been proved to lie in it. -/
theorem derivedCrossing_eq_mapped_character_ker_of_radical_le
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N)
    (hRB : primeRelativeRadical p (commutator G) ≤ N ⊓ commutator G)
    (χ : primeRelativeCharacters p (commutator G))
    (hχ : χ ∈ derivedCharactersVanishingOn p (N ⊓ commutator G)) (hχ0 : χ ≠ 0) :
    N ⊓ commutator G =
      (AddMonoidHom.toMultiplicativeRight χ.1).ker.map (commutator G).subtype := by
  have h := derivedCrossing_sup_radical_eq_mapped_character_ker
    p hker hG hpair N hnotND hnotDN χ hχ hχ0
  rwa [sup_eq_left.mpr hRB] at h

/-- The identifying character exists in the actual original vanishing
space; no numeric label or abstract quotient character is substituted. -/
theorem exists_derivedCrossing_character_kernel_join
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N) :
    ∃ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 ∧
      χ ∈ derivedCharactersVanishingOn p (N ⊓ commutator G) ∧
      (N ⊓ commutator G) ⊔ primeRelativeRadical p (commutator G) =
        (AddMonoidHom.toMultiplicativeRight χ.1).ker.map (commutator G).subtype := by
  obtain ⟨χ, hχ0, hspan⟩ := exists_derivedCharacter_spanning_of_crossing
    p hker hG hpair N hnotND hnotDN
  have hχ : χ ∈ derivedCharactersVanishingOn p (N ⊓ commutator G) := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self χ
  exact ⟨χ, hχ0, hχ, derivedCrossing_sup_radical_eq_mapped_character_ker
    p hker hG hpair N hnotND hnotDN χ hχ hχ0⟩

theorem exists_derivedCrossing_character_kernel_of_radical_le
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N)
    (hRB : primeRelativeRadical p (commutator G) ≤ N ⊓ commutator G) :
    ∃ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 ∧
      χ ∈ derivedCharactersVanishingOn p (N ⊓ commutator G) ∧
      N ⊓ commutator G =
        (AddMonoidHom.toMultiplicativeRight χ.1).ker.map (commutator G).subtype := by
  obtain ⟨χ, hχ0, hχ, he⟩ := exists_derivedCrossing_character_kernel_join
    p hker hG hpair N hnotND hnotDN
  exact ⟨χ, hχ0, hχ, by simpa only [sup_eq_left.mpr hRB] using he⟩

end SymmetricSubgroupAsymptotics
