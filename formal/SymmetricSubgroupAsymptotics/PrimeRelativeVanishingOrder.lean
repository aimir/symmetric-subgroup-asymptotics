import SymmetricSubgroupAsymptotics.PrimeRelativeCharacterDetection

/-! The complete original invariant characters vanishing on B give an
exact order factorization through the actual join B∨R_D. Surjectivity is
proved for evaluation on this character subspace, not assumed for a chosen
coordinate map or obtained by extending arbitrary characters of B. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G]
    (D : Subgroup G) [D.Normal]

/-- Evaluate the same original D on every actual invariant character
vanishing on B. The codomain is precisely the dual of that subspace. -/
def primeVanishingEvaluation (B : Subgroup G) : D →*
    Multiplicative (Module.Dual (ZMod p) (primeRelativeCharactersVanishingOn p D B)) :=
  retainedCharacterEvaluation p
    ((primeRelativeCharacters p D).subtype.comp
      (primeRelativeCharactersVanishingOn p D B).subtype)

@[simp] theorem primeVanishingEvaluation_apply
    (B : Subgroup G) (d : D) (χ : primeRelativeCharactersVanishingOn p D B) :
    (primeVanishingEvaluation p D B d).toAdd χ = χ.1.1 (Additive.ofMul d) := rfl

theorem primeVanishingEvaluation_surjective [Finite G] (B : Subgroup G) :
    Function.Surjective (primeVanishingEvaluation p D B) := by
  apply retainedCharacterEvaluation_surjective
  exact Subtype.val_injective.comp Subtype.val_injective

variable [Finite G]

/-- Equality is in the original ambient group, with the original
inclusion of D. The relative radical is retained when B does not contain it. -/
theorem primeVanishingEvaluation_ker_map
    (B : Subgroup G) (hBD : B ≤ D) :
    (primeVanishingEvaluation p D B).ker.map D.subtype = B ⊔ primeRelativeRadical p D := by
  apply le_antisymm
  · rintro x ⟨d, hd, rfl⟩
    apply (mem_sup_primeRelativeRadical_iff p D B hBD d).mpr
    intro χ hχ
    exact congrArg
      (fun f : Multiplicative
        (Module.Dual (ZMod p) (primeRelativeCharactersVanishingOn p D B)) =>
          f.toAdd ⟨χ, hχ⟩)
      (show primeVanishingEvaluation p D B d = 1 from hd)
  · intro x hx
    have hxD : x ∈ D := (sup_le hBD (primeRelativeRadical_le p D)) hx
    refine ⟨⟨x, hxD⟩, ?_, rfl⟩
    change primeVanishingEvaluation p D B ⟨x, hxD⟩ = 1
    apply Multiplicative.toAdd.injective
    ext χ
    exact (mem_sup_primeRelativeRadical_iff p D B hBD ⟨x, hxD⟩).mp hx χ.1 χ.2

/-- The exact factor counts all vanishing characters of the same
original D and the order of their actual detected subgroup. -/
theorem primeRelativeVanishing_card_factorization_join
    (B : Subgroup G) (hBD : B ≤ D) :
    Nat.card D =
      p ^ Module.finrank (ZMod p) (primeRelativeCharactersVanishingOn p D B) *
        Nat.card ↥(B ⊔ primeRelativeRadical p D) := by
  let f := primeVanishingEvaluation p D B
  have hk : Nat.card f.ker = Nat.card ↥(B ⊔ primeRelativeRadical p D) := by
    have h := Nat.card_congr (f.ker.equivMapOfInjective D.subtype D.subtype_injective).toEquiv
    rwa [primeVanishingEvaluation_ker_map p D B hBD] at h
  have hq : Nat.card (D ⧸ f.ker) =
      p ^ Module.finrank (ZMod p) (primeRelativeCharactersVanishingOn p D B) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      f (primeVanishingEvaluation_surjective p D B)).toEquiv]
    change Nat.card (Module.Dual (ZMod p) (primeRelativeCharactersVanishingOn p D B)) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Subspace.dual_finrank_eq,
      Nat.card_zmod]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rwa [hq, hk] at h

/-- Only actual radical containment permits using |B| instead of |B∨R|. -/
theorem primeRelativeVanishing_card_factorization
    (B : Subgroup G) (hBD : B ≤ D) (hRB : primeRelativeRadical p D ≤ B) :
    Nat.card D =
      p ^ Module.finrank (ZMod p) (primeRelativeCharactersVanishingOn p D B) * Nat.card B := by
  simpa only [sup_eq_left.mpr hRB] using
    primeRelativeVanishing_card_factorization_join p D B hBD

/-- For two actual normals with the same radical, complete vanishing
dimension and the original smaller head split the larger head exactly. -/
theorem primeRelativeVanishing_finrank_add_head_of_radical_eq
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D)
    (hR : primeRelativeRadical p B = primeRelativeRadical p D) :
    Module.finrank (ZMod p) (primeRelativeCharactersVanishingOn p D B) +
        Module.finrank (ZMod p) (primeRelativeCharacters p B) =
      Module.finrank (ZMod p) (primeRelativeCharacters p D) := by
  have hRB : primeRelativeRadical p D ≤ B := by
    rw [← hR]
    exact primeRelativeRadical_le p B
  have h := primeRelativeVanishing_card_factorization p D B hBD hRB
  rw [primeRelativeRadical_card_factorization p D,
    primeRelativeRadical_card_factorization p B, hR] at h
  apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := primeRelativeRadical p D))
  simpa only [pow_add, Nat.mul_assoc] using h.symm

end SymmetricSubgroupAsymptotics
