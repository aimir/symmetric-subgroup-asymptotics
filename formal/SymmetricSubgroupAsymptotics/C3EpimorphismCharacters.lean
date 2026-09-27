import SymmetricSubgroupAsymptotics.C3DirectAxisNormalized
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-!
# Epimorphisms onto the regular C3 action as oriented characters

The trivial-axis Goursat parameter is an arbitrary epimorphism onto C3; it
need not split.  This file identifies those epimorphisms exactly with the
nonzero ternary characters and proves that their quotient graphs agree with
the physical regular-C3 graph model.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {J : Type*} [Group J]

/-- A ternary character is onto exactly when it is nonzero.  This does not
assert that the epimorphism has a group-theoretic section. -/
theorem ternaryCharacter_surjective_iff_ne_zero (χ : PrimeCharacters 3 J) :
    Function.Surjective (ternaryCharacterHom χ) ↔ χ ≠ 0 := by
  constructor
  · intro hs hzero
    obtain ⟨x,hx⟩ := hs ternaryGenerator
    have he : ternaryGenerator = 1 := by
      rw [← hx]
      simp [ternaryCharacterHom,hzero]
    have ho := congrArg orderOf he
    rw [ternaryGenerator_order,orderOf_one] at ho
    omega
  · intro hχ
    have hcard : Nat.card TernaryCyclic = 3 := by
      simp [TernaryCyclic,Nat.card_eq_fintype_card]
    letI : Fact (Nat.card TernaryCyclic).Prime := ⟨by rw [hcard]; norm_num⟩
    rcases (ternaryCharacterHom χ).range.eq_bot_or_eq_top_of_prime_card with hr | hr
    · exfalso
      apply hχ
      apply AddMonoidHom.ext
      intro x
      have hx : ternaryCharacterHom χ x = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← hr]
        exact ⟨x,rfl⟩
      exact congrArg Multiplicative.toAdd hx
    · exact MonoidHom.range_eq_top.mp hr

/-- Literal epimorphisms onto C3 are exactly the nonzero oriented ternary
characters.  Nonsplit characters are deliberately retained. -/
def ternaryEpimorphismEquivNonzero :
    GroupEpimorphism J TernaryCyclic ≃
      {χ : PrimeCharacters 3 J // χ ≠ 0} where
  toFun β := ⟨AddMonoidHom.toMultiplicativeRight.symm β.1,
    (ternaryCharacter_surjective_iff_ne_zero _).mp β.2⟩
  invFun χ := ⟨ternaryCharacterHom χ.1,
    (ternaryCharacter_surjective_iff_ne_zero χ.1).mpr χ.2⟩
  left_inv β := by
    apply Subtype.ext
    rfl
  right_inv χ := by
    apply Subtype.ext
    rfl

/-- The corresponding literal epimorphism onto the regular permutation copy
of C3. -/
def c3EpimorphismOfCharacter (χ : {χ : PrimeCharacters 3 J // χ ≠ 0}) :
    GroupEpimorphism J ternaryRegularAction :=
  ⟨ternaryRegularEquiv.toMonoidHom.comp (ternaryCharacterHom χ.1),
    ternaryRegularEquiv.surjective.comp
      ((ternaryCharacter_surjective_iff_ne_zero χ.1).mpr χ.2)⟩

/-- The Goursat quotient graph of the regular-action epimorphism is exactly
the physical image of the oriented ternary character graph. -/
theorem c3Epimorphism_character_graph {Z : Type*}
    (K : Subgroup (Equiv.Perm Z))
    (χ : {χ : PrimeCharacters 3 K // χ ≠ 0}) :
    (ternaryActualGraph ⟨K,χ.1⟩).map
        (ternaryPhysicalCoordinateEquiv (Z := Z)).toMonoidHom =
      fusionQuotientGraph (MonoidHom.id ternaryRegularAction) K
        (c3EpimorphismOfCharacter χ).1 := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change y ∈ fusionQuotientGraph (MonoidHom.id TernaryCyclic) K
      (ternaryCharacterHom χ.1) at hy
    obtain ⟨j,hj,hq⟩ := hy
    refine ⟨j,hj,?_⟩
    change ternaryRegularEquiv y.1 =
      ternaryRegularEquiv (ternaryCharacterHom χ.1 j)
    exact congrArg ternaryRegularEquiv hq
  · rintro ⟨j,hj,hq⟩
    refine ⟨(ternaryRegularEquiv.symm x.1,x.2),?_,?_⟩
    · change (ternaryRegularEquiv.symm x.1,x.2) ∈
        fusionQuotientGraph (MonoidHom.id TernaryCyclic) K
          (ternaryCharacterHom χ.1)
      refine ⟨j,hj,?_⟩
      apply ternaryRegularEquiv.injective
      simpa using hq
    · apply Prod.ext
      · change ternaryRegularEquiv (ternaryRegularEquiv.symm x.1) = x.1
        exact ternaryRegularEquiv.apply_symm_apply x.1
      · rfl

end SymmetricSubgroupAsymptotics

end
