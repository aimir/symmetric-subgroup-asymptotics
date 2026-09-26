import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionForms

/-! Full original form separation excludes quotient-center directions
outside the derived group for every normal inside its relative radical.
The separating hypothesis quantifies over every actual invariant character. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)

theorem quotientCenterPreimage_le_commutator_of_full_separation
    (hsep : ∀ v : PrimeAbelianization p G,
      (∀ χ : primeRelativeCharacters p (commutator G),
        derivedEvaluationBilinearMap p hker χ v = 0) → v = 0)
    (N : Subgroup G) [N.Normal]
    (hN : N ≤ primeRelativeRadical p (commutator G)) :
    quotientCenterPreimage N ≤ commutator G := by
  apply (primeDerivedImage_eq_bot_iff_le_commutator p hker _).mp
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  apply hsep
  intro χ
  have hχ : χ ∈ derivedCharactersVanishingOn p N := by
    rw [derivedCharactersVanishingOn_eq_top_of_le_radical p N hN]
    trivial
  exact derivedCharactersVanishingOn_le_center_joint p hker N hχ v hv

end SymmetricSubgroupAsymptotics
