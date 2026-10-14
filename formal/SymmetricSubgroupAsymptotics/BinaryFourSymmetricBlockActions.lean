import SymmetricSubgroupAsymptotics.BinaryFourFullBlockActions

/-! The reflection extending the full four-block A4 module to S4.
The reflection on the two Klein coordinates differs from its action on
the local two-dimensional module. All linear identities are checked on
eight basis vectors; no invariant-subspace enumeration is used. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourSymmetricBlockActions

open BinaryFourBlockAugmentation BinaryFourFullBlockCoordinates SemidirectProduct

def fullS : FullCoordinates ≃ₗ[Scalar] FullCoordinates where
  toFun x := ![x 1 + x 2, x 0 + x 2 + x 3, x 2 + x 3, x 3,
    x 3 + x 4, x 2 + x 3 + x 4 + x 5, x 7, x 6]
  invFun x := ![x 1 + x 2, x 0 + x 2 + x 3, x 2 + x 3, x 3,
    x 3 + x 4, x 2 + x 3 + x 4 + x 5, x 7, x 6]
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel,
        show (4 : Scalar) = 0 from by decide +kernel,
        mul_zero, zero_add, add_zero]
  right_inv := by
    intro x
    ext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel,
        show (4 : Scalar) = 0 from by decide +kernel,
        mul_zero, zero_add, add_zero]
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring

theorem fullS_square : fullS ^ 2 = 1 := by
  apply linearEquiv_ext_basis
  intro i
  revert i
  decide +kernel

/-- The local reflection swaps the two entries; the block reflection is (23). -/
theorem fullS_decode (x : FullCoordinates) (b : Fin 4) (i : Fin 2) :
    fullDecode (fullS x) b i = fullDecode x (Equiv.swap 2 3 b) (Equiv.swap 0 1 i) := by
  fin_cases b <;> fin_cases i <;>
    simp [fullDecode, fullS, Equiv.swap_apply_def] <;> ring_nf <;>
    simp only [show (2 : Scalar) = 0 from by decide +kernel,
      show (3 : Scalar) = 1 from by decide +kernel,
      mul_zero, mul_one, add_zero]

def reflectComplement (r : Complement) : Complement :=
  ⟨Multiplicative.ofAdd ![r.left.toAdd 0, r.left.toAdd 0 + r.left.toAdd 1],
    Multiplicative.ofAdd (-r.right.toAdd)⟩

theorem reflectComplement_involutive : Function.Involutive reflectComplement := by
  intro r
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp [reflectComplement]
  · apply Multiplicative.toAdd.injective
    simp [reflectComplement]

def complementReflection : MulAut Complement where
  toFun := reflectComplement
  invFun := reflectComplement
  left_inv := reflectComplement_involutive
  right_inv := reflectComplement_involutive
  map_mul' r s := by
    rcases r with ⟨p, z⟩
    rcases s with ⟨q, w⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      ext i
      revert p z q w i
      decide +kernel
    · apply Multiplicative.toAdd.injective
      simp [reflectComplement, add_comm]

theorem complementReflection_square : complementReflection ^ 2 = 1 := by
  apply MulEquiv.ext
  intro r
  exact reflectComplement_involutive r

abbrev Binary := Multiplicative (ZMod 2)

def complementBinaryAction : Binary →* MulAut Complement :=
  powersHom 2 complementReflection complementReflection_square

abbrev SymmetricComplement := Complement ⋊[complementBinaryAction] Binary

instance : Finite SymmetricComplement :=
  Finite.of_equiv (Complement × Binary) SemidirectProduct.equivProd.symm

def fullBinary : Binary →* (FullCoordinates ≃ₗ[Scalar] FullCoordinates) :=
  powersHom 2 fullS fullS_square

theorem reflectionCompatibility (r : Complement) :
    fullComplementLinear (complementReflection r) =
      fullS * fullComplementLinear r * fullS⁻¹ := by
  apply linearEquiv_ext_basis
  intro i
  rcases r with ⟨p, z⟩
  revert p z i
  decide +kernel

theorem symmetricCompatibility (z : Binary) :
    fullComplementLinear.comp (complementBinaryAction z).toMonoidHom =
      (MulAut.conj (fullBinary z)).toMonoidHom.comp fullComplementLinear := by
  apply MonoidHom.ext
  intro r
  apply linearEquiv_ext_basis
  intro i
  rcases r with ⟨p, w⟩
  revert z p w i
  decide +kernel

def symmetricLinear : SymmetricComplement →*
    (FullCoordinates ≃ₗ[Scalar] FullCoordinates) :=
  SemidirectProduct.lift fullComplementLinear fullBinary symmetricCompatibility

def symmetricAction : SymmetricComplement →* MulAut (Multiplicative FullCoordinates) where
  toFun r := (symmetricLinear r).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f : FullCoordinates ≃ₗ[Scalar] FullCoordinates =>
      Multiplicative.ofAdd (f x.toAdd)) symmetricLinear.map_one
  map_mul' r s := by
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f : FullCoordinates ≃ₗ[Scalar] FullCoordinates =>
      Multiplicative.ofAdd (f x.toAdd)) (symmetricLinear.map_mul r s)

abbrev SymmetricAmbient := Multiplicative FullCoordinates ⋊[symmetricAction] SymmetricComplement

instance : Finite SymmetricAmbient :=
  Finite.of_equiv (Multiplicative FullCoordinates × SymmetricComplement)
    SemidirectProduct.equivProd.symm

end BinaryFourSymmetricBlockActions
end SymmetricSubgroupAsymptotics

end
