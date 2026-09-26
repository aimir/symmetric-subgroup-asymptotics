import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionForms
import SymmetricSubgroupAsymptotics.PrimeNormalIntervalCharacters
import SymmetricSubgroupAsymptotics.StarAlternatingParameterCapacity

/-! Proper original derived intersections supply their own nonzero
vanishing characters in finite p-groups. Combining those actual characters
with the original form family bounds every quotient direction at once.
No normal menu, numerical character-separation premise, or extendibility
of characters from the intersection is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

theorem derivedCharactersVanishingOn_ne_bot_of_lt (hG : IsPGroup p G)
    (B : Subgroup G) [B.Normal] (hBD : B < commutator G) :
    derivedCharactersVanishingOn p B ≠ ⊥ := by
  obtain ⟨χ, hχ, hv⟩ := pGroup_exists_nonzero_derivedCharacter_vanishing hG B hBD
  intro hz
  have hm : χ ∈ derivedCharactersVanishingOn p B := hv
  rw [hz] at hm
  exact hχ hm

theorem derivedCharactersVanishingOn_one_le_of_lt (hG : IsPGroup p G)
    (B : Subgroup G) [B.Normal] (hBD : B < commutator G) :
    1 ≤ Module.finrank (ZMod p) (derivedCharactersVanishingOn p B) :=
  Submodule.one_le_finrank_iff.mpr
    (derivedCharactersVanishingOn_ne_bot_of_lt p hG B hBD)

omit [Finite G] in
theorem derivedIntersection_lt_of_not_derived_le (N : Subgroup G)
    (hN : ¬commutator G ≤ N) : N ⊓ commutator G < commutator G := by
  apply lt_of_le_of_ne inf_le_right
  intro he
  apply hN
  rw [← he]
  exact inf_le_left

theorem primeDerivedImage_finrank_le_of_proper_intersection
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (hG : IsPGroup p G) (a : ℕ)
    (hsingle : ∀ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 →
      Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker ≤ a)
    (N : Subgroup G) [N.Normal] (hN : ¬commutator G ≤ N) :
    Module.finrank (ZMod p) (primeDerivedImage p N) ≤ a :=
  derivedCharactersVanishingOn_image_finrank_le_of_one_le p hker a hsingle
    (N ⊓ commutator G) N le_rfl
    (derivedCharactersVanishingOn_one_le_of_lt p hG _
      (derivedIntersection_lt_of_not_derived_le N hN))

section Star

variable {U : Type*} [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]

theorem primeDerivedImage_finrank_add_vanishing_le_of_star
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (eL : primeRelativeCharacters p (commutator G) ≃ₗ[ZMod p] Module.Dual (ZMod p) U)
    (eV : PrimeAbelianization p G ≃ₗ[ZMod p] U × ZMod p)
    (hF : ∀ χ x y, derivedEvaluationBilinearMap p hker χ x y =
      starAlternatingFamily (eL χ) (eV x) (eV y))
    (B N : Subgroup G) [N.Normal] (hNB : N ⊓ commutator G ≤ B)
    (hB : derivedCharactersVanishingOn p B ≠ ⊥) :
    Module.finrank (ZMod p) (primeDerivedImage p N) +
      Module.finrank (ZMod p) (derivedCharactersVanishingOn p B) ≤ Module.finrank (ZMod p) U :=
  linearFamily_finrank_add_parameter_le_of_star
    (derivedEvaluationBilinearMap p hker) eL eV hF
    (derivedCharactersVanishingOn p B) (primeDerivedImage p N) hB
    (derivedCharactersVanishingOn_le_joint p hker B N hNB)

theorem primeDerivedImage_finrank_add_one_le_of_proper_intersection_star
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (hG : IsPGroup p G)
    (eL : primeRelativeCharacters p (commutator G) ≃ₗ[ZMod p] Module.Dual (ZMod p) U)
    (eV : PrimeAbelianization p G ≃ₗ[ZMod p] U × ZMod p)
    (hF : ∀ χ x y, derivedEvaluationBilinearMap p hker χ x y =
      starAlternatingFamily (eL χ) (eV x) (eV y))
    (N : Subgroup G) [N.Normal] (hN : ¬commutator G ≤ N) :
    Module.finrank (ZMod p) (primeDerivedImage p N) + 1 ≤ Module.finrank (ZMod p) U := by
  have hB := derivedIntersection_lt_of_not_derived_le N hN
  have h := primeDerivedImage_finrank_add_vanishing_le_of_star p hker eL eV hF
    (N ⊓ commutator G) N le_rfl (derivedCharactersVanishingOn_ne_bot_of_lt p hG _ hB)
  exact (Nat.add_le_add_left (derivedCharactersVanishingOn_one_le_of_lt p hG _ hB) _).trans h

end Star
end SymmetricSubgroupAsymptotics
