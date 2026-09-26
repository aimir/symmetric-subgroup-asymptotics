import SymmetricSubgroupAsymptotics.PrimeDerivedCrossingDetection
import SymmetricSubgroupAsymptotics.PrimeDerivedCharacterKernelQuotient

/-! Exact correlated quotient invariants for crossing original normals.
Pair separation reduces the complete vanishing space to one line. Actual
radical containment identifies the original intersection with its character
kernel, and a uniform exact single-form radical dimension determines the
center of the same original quotient. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Every non-derived original normal has a positive actual image
dimension when the evaluation kernel is the actual derived subgroup. -/
theorem primeDerivedImage_one_le_of_not_le
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (N : Subgroup G) (hnot : ¬N ≤ commutator G) :
    1 ≤ Module.finrank (ZMod p) (primeDerivedImage p N) := by
  apply Submodule.one_le_finrank_iff.mpr
  intro hz
  exact hnot ((primeDerivedImage_eq_bot_iff_le_commutator p hker N).mp hz)

/-- All fields belong to the same original N. Radical containment is
explicit and cannot be replaced by detection of the join with the radical. -/
theorem derivedCrossing_exact_quotient_invariants
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (hG : IsPGroup p G)
    (hpair : ∀ v : Fin 2 → primeRelativeCharacters p (commutator G),
      LinearIndependent (ZMod p) v →
      (derivedEvaluationBilinearMap p hker (v 0)).ker ⊓
        (derivedEvaluationBilinearMap p hker (v 1)).ker = ⊥)
    (r : ℕ)
    (hr : ∀ χ : primeRelativeCharacters p (commutator G), χ ≠ 0 →
      Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker = r)
    (N : Subgroup G) [N.Normal]
    (hnotND : ¬N ≤ commutator G) (hnotDN : ¬commutator G ≤ N)
    (hRB : primeRelativeRadical p (commutator G) ≤ N ⊓ commutator G) :
    1 ≤ Module.finrank (ZMod p) (primeDerivedImage p N) ∧
      Module.finrank (ZMod p) (primeDerivedImage p N) ≤ r ∧
      p * Nat.card ↥(N ⊓ commutator G) = Nat.card (commutator G) ∧
      Nat.card (Subgroup.center (G ⧸ N)) =
        p ^ (r + 1 - Module.finrank (ZMod p) (primeDerivedImage p N)) ∧
      Nat.card (commutator (G ⧸ N)) = p := by
  obtain ⟨χ, hχ, _, hNK⟩ := exists_derivedCrossing_character_kernel_of_radical_le
    p hker hG hpair N hnotND hnotDN hRB
  change N ⊓ commutator G = primeRelativeCharacterKernel p (commutator G) χ at hNK
  refine ⟨primeDerivedImage_one_le_of_not_le p hker N hnotND, ?_, ?_, ?_, ?_⟩
  · simpa only [hr χ hχ] using
      primeDerivedImage_finrank_le_characterKernel_radical p hker χ N hNK
  · rw [hNK]
    exact primeRelativeCharacterKernel_card_factorization p (commutator G) χ hχ
  · simpa only [hr χ hχ] using
      quotientCenter_card_eq_pow_of_derived_character_kernel p hker χ hχ N hNK
  · exact quotientCommutator_card_eq_prime_of_derived_character_kernel p χ hχ N hNK

end SymmetricSubgroupAsymptotics
