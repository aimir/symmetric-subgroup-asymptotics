import SymmetricSubgroupAsymptotics.PrimeDerivedCharacterKernelCenter

/-! Exact quotient invariants when an original normal subgroup meets the
original derived subgroup in the literal kernel of a nonzero invariant
character. The quotient center and derived group retain the same N.
The center exponent uses the actual image dimension of N and the actual
radical of this character's commutator form; their dimension comparison
is proved from original centrality, rather than supplied numerically. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

private theorem centerPreimage_intersection_eq_characterKernel
    (χ : primeRelativeCharacters p (commutator G))
    (N : Subgroup G) [N.Normal]
    (hNK : N ⊓ commutator G = primeRelativeCharacterKernel p (commutator G) χ) :
    quotientCenterPreimage (N ⊓ commutator G) =
      quotientCenterPreimage (primeRelativeCharacterKernel p (commutator G) χ) := by
  ext x
  rw [mem_quotientCenterPreimage_iff_all_commutators,
    mem_quotientCenterPreimage_iff_all_commutators]
  simp only [hNK]

/-- The derived subgroup of the original quotient has order p when the
actual derived intersection is the kernel of a nonzero original character. -/
theorem quotientCommutator_card_eq_prime_of_derived_character_kernel
    (χ : primeRelativeCharacters p (commutator G)) (hχ : χ ≠ 0)
    (N : Subgroup G) [N.Normal]
    (hNK : N ⊓ commutator G = primeRelativeCharacterKernel p (commutator G) χ) :
    Nat.card (commutator (G ⧸ N)) = p := by
  have hc := quotientCommutator_card_mul_inf N
  rw [hNK] at hc
  have hk := primeRelativeCharacterKernel_card_factorization p (commutator G) χ hχ
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.card_pos (α := primeRelativeCharacterKernel p (commutator G) χ))
    (hc.trans hk.symm)

variable (hker : (primeAbelianizationGroupMap p G).ker = commutator G)

/-- Every direction coming from this actual N belongs to the radical of
the same actual character form. No converse image-containment is assumed. -/
theorem primeDerivedImage_le_characterKernel_form_radical
    (χ : primeRelativeCharacters p (commutator G))
    (N : Subgroup G) [N.Normal]
    (hNK : N ⊓ commutator G = primeRelativeCharacterKernel p (commutator G) χ) :
    primeDerivedImage p N ≤ (derivedEvaluationBilinearMap p hker χ).ker := by
  have hNC : N ≤ quotientCenterPreimage
      (primeRelativeCharacterKernel p (commutator G) χ) := by
    rw [← centerPreimage_intersection_eq_characterKernel p χ N hNK,
      ← quotientCenterPreimage_eq_inf_commutator N]
    exact le_quotientCenterPreimage N
  intro v hv
  obtain ⟨n, rfl⟩ := (mem_primeDerivedImage_iff p N v).mp hv
  exact (mem_quotientCenterPreimage_characterKernel_iff p hker χ (n : G)).mp
    (hNC n.2)

theorem primeDerivedImage_finrank_le_characterKernel_radical
    (χ : primeRelativeCharacters p (commutator G))
    (N : Subgroup G) [N.Normal]
    (hNK : N ⊓ commutator G = primeRelativeCharacterKernel p (commutator G) χ) :
    Module.finrank (ZMod p) (primeDerivedImage p N) ≤
      Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker :=
  Submodule.finrank_mono
    (primeDerivedImage_le_characterKernel_form_radical p hker χ N hNK)

/-- Exact multiplicative center correlation, before any subtraction of
dimensions. The canceled factor is the order of the actual intersection. -/
theorem quotientCenter_card_mul_pow_of_derived_character_kernel
    (χ : primeRelativeCharacters p (commutator G)) (hχ : χ ≠ 0)
    (N : Subgroup G) [N.Normal]
    (hNK : N ⊓ commutator G = primeRelativeCharacterKernel p (commutator G) χ) :
    Nat.card (Subgroup.center (G ⧸ N)) *
        p ^ Module.finrank (ZMod p) (primeDerivedImage p N) =
      p ^ (Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker + 1) := by
  have hn := primeDerivedImage_pow_finrank_mul_intersection p hker N
  rw [hNK] at hn
  have hz := quotientCenter_card_mul_inf_commutator N
  rw [centerPreimage_intersection_eq_characterKernel p χ N hNK,
    quotientCenterPreimage_characterKernel_card p hker χ] at hz
  have hk := primeRelativeCharacterKernel_card_factorization p (commutator G) χ hχ
  rw [← hn, ← hk] at hz
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.card_pos (α := primeRelativeCharacterKernel p (commutator G) χ))
  calc
    (Nat.card (Subgroup.center (G ⧸ N)) *
        p ^ Module.finrank (ZMod p) (primeDerivedImage p N)) *
        Nat.card (primeRelativeCharacterKernel p (commutator G) χ) =
      Nat.card (Subgroup.center (G ⧸ N)) *
        (p ^ Module.finrank (ZMod p) (primeDerivedImage p N) *
          Nat.card (primeRelativeCharacterKernel p (commutator G) χ)) :=
      Nat.mul_assoc _ _ _
    _ = p ^ Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker *
        (p * Nat.card (primeRelativeCharacterKernel p (commutator G) χ)) := hz
    _ = p ^ (Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker + 1) *
        Nat.card (primeRelativeCharacterKernel p (commutator G) χ) := by
      rw [pow_succ, Nat.mul_assoc]

/-- The actual image-radical inclusion makes the center exponent exact:
there is no truncated-subtraction approximation or independent choice of N. -/
theorem quotientCenter_card_eq_pow_of_derived_character_kernel
    (χ : primeRelativeCharacters p (commutator G)) (hχ : χ ≠ 0)
    (N : Subgroup G) [N.Normal]
    (hNK : N ⊓ commutator G = primeRelativeCharacterKernel p (commutator G) χ) :
    Nat.card (Subgroup.center (G ⧸ N)) =
      p ^ (Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker + 1 -
        Module.finrank (ZMod p) (primeDerivedImage p N)) := by
  have hwr := primeDerivedImage_finrank_le_characterKernel_radical p hker χ N hNK
  have hwr' := hwr.trans (Nat.le_succ
    (Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker))
  apply Nat.eq_of_mul_eq_mul_right
    (pow_pos (Fact.out : p.Prime).pos (Module.finrank (ZMod p) (primeDerivedImage p N)))
  calc
    Nat.card (Subgroup.center (G ⧸ N)) *
        p ^ Module.finrank (ZMod p) (primeDerivedImage p N) =
      p ^ (Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker + 1) :=
      quotientCenter_card_mul_pow_of_derived_character_kernel p hker χ hχ N hNK
    _ = p ^ (Module.finrank (ZMod p) (derivedEvaluationBilinearMap p hker χ).ker + 1 -
          Module.finrank (ZMod p) (primeDerivedImage p N)) *
        p ^ Module.finrank (ZMod p) (primeDerivedImage p N) := by
      rw [← pow_add, Nat.sub_add_cancel hwr']

end SymmetricSubgroupAsymptotics
