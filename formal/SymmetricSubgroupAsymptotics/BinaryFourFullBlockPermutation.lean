import SymmetricSubgroupAsymptotics.BinaryFourFullBlockActions
import SymmetricSubgroupAsymptotics.BinaryFourAugmentationPermutation

/-! The full block module acts on the original sixteen points in the
same chart as the checked augmentation module. Conjugation is tested only
on the eight displayed basis translations and extended as a homomorphism. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

def fullBasis (i : Fin 8) : FullCoordinates := Pi.single i 1

theorem fullCoordinate_word (x : FullCoordinates) :
    Multiplicative.ofAdd x =
      Multiplicative.ofAdd (fullBasis 0) ^ (x 0).val *
      Multiplicative.ofAdd (fullBasis 1) ^ (x 1).val *
      Multiplicative.ofAdd (fullBasis 2) ^ (x 2).val *
      Multiplicative.ofAdd (fullBasis 3) ^ (x 3).val *
      Multiplicative.ofAdd (fullBasis 4) ^ (x 4).val *
      Multiplicative.ofAdd (fullBasis 5) ^ (x 5).val *
      Multiplicative.ofAdd (fullBasis 6) ^ (x 6).val *
      Multiplicative.ofAdd (fullBasis 7) ^ (x 7).val := by
  apply Multiplicative.toAdd.injective
  ext i
  simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, Pi.add_apply, Pi.smul_apply]
  fin_cases i <;> simp [fullBasis, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem fullHom_ext_basis {H : Type} [Group H]
    (f g : Multiplicative FullCoordinates →* H)
    (h : ∀ i : Fin 8, f (Multiplicative.ofAdd (fullBasis i)) =
      g (Multiplicative.ofAdd (fullBasis i))) : f = g := by
  apply MonoidHom.ext
  intro x
  have hx := fullCoordinate_word x.toAdd
  rw [ofAdd_toAdd] at hx
  rw [hx]
  simp only [map_mul, map_pow, h]

def fullDecodeHom : Multiplicative FullCoordinates →* Multiplicative
    BinaryFourBlockAugmentation.Module := fullChart.toAddEquiv.toMultiplicative.toMonoidHom

def fullTranslations : Multiplicative FullCoordinates →* Equiv.Perm (Fin 16) :=
  translation.comp fullDecodeHom

theorem fullTranslations_injective : Function.Injective fullTranslations :=
  translation_injective.comp fullChart.toAddEquiv.toMultiplicative.injective

theorem fullTranslations_include (x : Coordinates) :
    fullTranslations (Multiplicative.ofAdd (includeAugmentation x)) =
      translations (Multiplicative.ofAdd x) := by
  change translation (Multiplicative.ofAdd (fullDecode (includeAugmentation x))) =
    translation (Multiplicative.ofAdd (decode x))
  rw [fullDecode_include]

theorem fullConjugate_u (x : FullCoordinates) :
    uPerm * fullTranslations (Multiplicative.ofAdd x) * uPerm⁻¹ =
      fullTranslations (Multiplicative.ofAdd (fullU x)) := by
  have h := fullHom_ext_basis
    ((MulAut.conj uPerm).toMonoidHom.comp fullTranslations)
    (fullTranslations.comp fullU.toAddEquiv.toMultiplicative.toMonoidHom) (by
      intro j
      apply Equiv.ext
      intro i
      revert j i
      decide +kernel)
  exact congrArg (fun f : Multiplicative FullCoordinates →* Equiv.Perm (Fin 16) =>
    f (Multiplicative.ofAdd x)) h

theorem fullConjugate_v (x : FullCoordinates) :
    vPerm * fullTranslations (Multiplicative.ofAdd x) * vPerm⁻¹ =
      fullTranslations (Multiplicative.ofAdd (fullV x)) := by
  have h := fullHom_ext_basis
    ((MulAut.conj vPerm).toMonoidHom.comp fullTranslations)
    (fullTranslations.comp fullV.toAddEquiv.toMultiplicative.toMonoidHom) (by
      intro j
      apply Equiv.ext
      intro i
      revert j i
      decide +kernel)
  exact congrArg (fun f : Multiplicative FullCoordinates →* Equiv.Perm (Fin 16) =>
    f (Multiplicative.ofAdd x)) h

theorem fullConjugate_c (x : FullCoordinates) :
    cPerm * fullTranslations (Multiplicative.ofAdd x) * cPerm⁻¹ =
      fullTranslations (Multiplicative.ofAdd (fullC x)) := by
  have h := fullHom_ext_basis
    ((MulAut.conj cPerm).toMonoidHom.comp fullTranslations)
    (fullTranslations.comp fullC.toAddEquiv.toMultiplicative.toMonoidHom) (by
      intro j
      apply Equiv.ext
      intro i
      revert j i
      decide +kernel)
  exact congrArg (fun f : Multiplicative FullCoordinates →* Equiv.Perm (Fin 16) =>
    f (Multiplicative.ofAdd x)) h

theorem fullConjugate_power (P : Equiv.Perm (Fin 16))
    (L : FullCoordinates ≃ₗ[Scalar] FullCoordinates)
    (h : ∀ x, P * fullTranslations (Multiplicative.ofAdd x) * P⁻¹ =
      fullTranslations (Multiplicative.ofAdd (L x))) (n : ℕ) (x : FullCoordinates) :
    P ^ n * fullTranslations (Multiplicative.ofAdd x) * (P ^ n)⁻¹ =
      fullTranslations (Multiplicative.ofAdd ((L ^ n) x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ']
      calc
        (P * P ^ n) * fullTranslations (Multiplicative.ofAdd x) * (P * P ^ n)⁻¹ =
          P * (P ^ n * fullTranslations (Multiplicative.ofAdd x) * (P ^ n)⁻¹) * P⁻¹ := by
            group
        _ = P * fullTranslations (Multiplicative.ofAdd ((L ^ n) x)) * P⁻¹ := by rw [ih]
        _ = _ := h _

theorem fullConjugate_klein (p : Klein) (x : FullCoordinates) :
    kleinPermutation p * fullTranslations (Multiplicative.ofAdd x) *
        (kleinPermutation p)⁻¹ =
      fullTranslations (Multiplicative.ofAdd (fullKlein p x)) := by
  change (uPerm ^ (p.toAdd 0).val * vPerm ^ (p.toAdd 1).val) *
    fullTranslations (Multiplicative.ofAdd x) *
    (uPerm ^ (p.toAdd 0).val * vPerm ^ (p.toAdd 1).val)⁻¹ = _
  calc
    _ = uPerm ^ (p.toAdd 0).val *
        (vPerm ^ (p.toAdd 1).val * fullTranslations (Multiplicative.ofAdd x) *
          (vPerm ^ (p.toAdd 1).val)⁻¹) * (uPerm ^ (p.toAdd 0).val)⁻¹ := by group
    _ = fullTranslations (Multiplicative.ofAdd
        ((fullU ^ (p.toAdd 0).val) ((fullV ^ (p.toAdd 1).val) x))) := by
      rw [fullConjugate_power vPerm fullV fullConjugate_v,
        fullConjugate_power uPerm fullU fullConjugate_u]
    _ = _ := by
      change fullTranslations (Multiplicative.ofAdd
        ((fullU ^ (p.toAdd 0).val * fullV ^ (p.toAdd 1).val) x)) = _
      rw [fullKlein_formula]

theorem fullConjugate_complement (r : Complement) (x : FullCoordinates) :
    complementPermutation r * fullTranslations (Multiplicative.ofAdd x) *
        (complementPermutation r)⁻¹ =
      fullTranslations (Multiplicative.ofAdd (fullComplementLinear r x)) := by
  change (kleinPermutation r.left * cPerm ^ r.right.toAdd.val) *
      fullTranslations (Multiplicative.ofAdd x) *
      (kleinPermutation r.left * cPerm ^ r.right.toAdd.val)⁻¹ = _
  calc
    _ = kleinPermutation r.left *
      (cPerm ^ r.right.toAdd.val * fullTranslations (Multiplicative.ofAdd x) *
        (cPerm ^ r.right.toAdd.val)⁻¹) * (kleinPermutation r.left)⁻¹ := by group
    _ = fullTranslations (Multiplicative.ofAdd
        (fullKlein r.left ((fullC ^ r.right.toAdd.val) x))) := by
      rw [fullConjugate_power cPerm fullC fullConjugate_c, fullConjugate_klein]
    _ = _ := rfl

def fullPermutation : Ambient →* Equiv.Perm (Fin 16) :=
  SemidirectProduct.lift fullTranslations complementPermutation (by
    intro r
    apply MonoidHom.ext
    intro x
    exact (fullConjugate_complement r x.toAdd).symm)

theorem fullPermutation_inl (x : Multiplicative FullCoordinates) :
    fullPermutation (inl x) = fullTranslations x :=
  SemidirectProduct.lift_inl _ _ _ x

theorem fullPermutation_u : fullPermutation (inr uElement) = uPerm := by
  rw [fullPermutation, SemidirectProduct.lift_inr]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem fullPermutation_v : fullPermutation (inr vElement) = vPerm := by
  rw [fullPermutation, SemidirectProduct.lift_inr]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem fullPermutation_c : fullPermutation (inr cElement) = cPerm := by
  rw [fullPermutation, SemidirectProduct.lift_inr]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
