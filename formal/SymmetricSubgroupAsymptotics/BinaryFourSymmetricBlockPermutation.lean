import SymmetricSubgroupAsymptotics.BinaryFourSymmetricBlockActions
import SymmetricSubgroupAsymptotics.BinaryFourFullBlockPermutation

/-! The reflection extension acts on the actual sixteen points through
the same reversible chart as the four-block translation module. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourSymmetricBlockActions

open BinaryFourBlockAugmentation BinaryFourFullBlockCoordinates SemidirectProduct

def localReflection : Local ≃ₗ[Scalar] Local where
  toFun x := ![x 1, x 0]
  invFun x := ![x 1, x 0]
  left_inv := by intro x; ext i; fin_cases i <;> rfl
  right_inv := by intro x; ext i; fin_cases i <;> rfl
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

def sPerm : Equiv.Perm (Fin 16) :=
  pointEquiv.permCongr ((Equiv.swap 2 3).prodCongr localReflection.toEquiv)

theorem sPerm_square : sPerm ^ 2 = 1 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

def binaryPermutation : Binary →* Equiv.Perm (Fin 16) :=
  powersHom 2 sPerm sPerm_square

theorem symmetricPermutationCompatibility (z : Binary) :
    complementPermutation.comp (complementBinaryAction z).toMonoidHom =
      (MulAut.conj (binaryPermutation z)).toMonoidHom.comp complementPermutation := by
  apply MonoidHom.ext
  intro r
  apply Equiv.ext
  intro i
  rcases r with ⟨p, w⟩
  revert z p w i
  decide +kernel

def symmetricComplementPermutation : SymmetricComplement →* Equiv.Perm (Fin 16) :=
  SemidirectProduct.lift complementPermutation binaryPermutation
    symmetricPermutationCompatibility

theorem fullConjugate_s (x : FullCoordinates) :
    sPerm * fullTranslations (Multiplicative.ofAdd x) * sPerm⁻¹ =
      fullTranslations (Multiplicative.ofAdd (fullS x)) := by
  have h := fullHom_ext_basis
    ((MulAut.conj sPerm).toMonoidHom.comp fullTranslations)
    (fullTranslations.comp fullS.toAddEquiv.toMultiplicative.toMonoidHom) (by
      intro j
      apply Equiv.ext
      intro i
      revert j i
      decide +kernel)
  exact congrArg (fun f : Multiplicative FullCoordinates →* Equiv.Perm (Fin 16) =>
    f (Multiplicative.ofAdd x)) h

theorem fullConjugate_symmetric (r : SymmetricComplement) (x : FullCoordinates) :
    symmetricComplementPermutation r * fullTranslations (Multiplicative.ofAdd x) *
        (symmetricComplementPermutation r)⁻¹ =
      fullTranslations (Multiplicative.ofAdd (symmetricLinear r x)) := by
  change (complementPermutation r.left * sPerm ^ r.right.toAdd.val) *
      fullTranslations (Multiplicative.ofAdd x) *
      (complementPermutation r.left * sPerm ^ r.right.toAdd.val)⁻¹ = _
  calc
    _ = complementPermutation r.left *
      (sPerm ^ r.right.toAdd.val * fullTranslations (Multiplicative.ofAdd x) *
        (sPerm ^ r.right.toAdd.val)⁻¹) * (complementPermutation r.left)⁻¹ := by group
    _ = fullTranslations (Multiplicative.ofAdd
        (fullComplementLinear r.left ((fullS ^ r.right.toAdd.val) x))) := by
      rw [fullConjugate_power sPerm fullS fullConjugate_s, fullConjugate_complement]
    _ = _ := rfl

def symmetricPermutation : SymmetricAmbient →* Equiv.Perm (Fin 16) :=
  SemidirectProduct.lift fullTranslations symmetricComplementPermutation (by
    intro r
    apply MonoidHom.ext
    intro x
    exact (fullConjugate_symmetric r x.toAdd).symm)

theorem symmetricPermutation_inl (x : Multiplicative FullCoordinates) :
    symmetricPermutation (inl x) = fullTranslations x :=
  SemidirectProduct.lift_inl _ _ _ x

theorem symmetricPermutation_old (r : Complement) :
    symmetricPermutation (inr (inl r)) = complementPermutation r := by
  rw [symmetricPermutation, SemidirectProduct.lift_inr,
    symmetricComplementPermutation, SemidirectProduct.lift_inl]

theorem symmetricPermutation_reflection :
    symmetricPermutation (inr (inr (Multiplicative.ofAdd (1 : ZMod 2)))) = sPerm := by
  rw [symmetricPermutation, SemidirectProduct.lift_inr,
    symmetricComplementPermutation, SemidirectProduct.lift_inr]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

end BinaryFourSymmetricBlockActions
end SymmetricSubgroupAsymptotics

end
