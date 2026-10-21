import SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
import Mathlib.Data.Nat.Bitwise

/-! Actual point translations become squarefree derivatives in the
reversible polynomial coordinates. The finite identity is on 4 × 16
individual monomials and their original point values. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth

def flipIndex (i : Fin 4) (x : Fin 16) : Fin 16 :=
  ⟨(x.val ^^^ 2 ^ i.val) % 16, Nat.mod_lt _ (by decide)⟩

def removeIndex (i : Fin 4) (a : Fin 16) : Fin 16 :=
  ⟨a.val - 2 ^ i.val, lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩

def translate (i : Fin 4) : V →ₗ[ZMod 2] V where
  toFun v := fun x => v (flipIndex i x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flipIndex_involutive : ∀ i : Fin 4, Function.Involutive (flipIndex i) := by
  change ∀ (i : Fin 4) (x : Fin 16), flipIndex i (flipIndex i x) = x
  decide

def pointTranslation (i : Fin 4) : Equiv.Perm (Fin 16) where
  toFun := flipIndex i
  invFun := flipIndex i
  left_inv := flipIndex_involutive i
  right_inv := flipIndex_involutive i

theorem translate_sub_monomial : ∀ (i : Fin 4) (a : Fin 16),
    translate i (monomial (support a)) - monomial (support a) =
      if i ∈ support a then monomial (support (removeIndex i a)) else 0 := by decide +kernel

/-- This is the operator obtained from an actual point translation minus
the identity; it is not an asserted action of a fictitious group element. -/
def derivative (i : Fin 4) : V →ₗ[ZMod 2] V :=
  evaluate.comp (((translate i) - LinearMap.id).comp evaluate)

theorem evaluate_monomial (a : Fin 16) :
    evaluate (monomial (support a)) = Pi.single a 1 := by
  rw [← evaluate_basis]
  exact evaluate_involutive _

theorem derivative_basis (i : Fin 4) (a : Fin 16) :
    derivative i (Pi.single a 1) =
      if i ∈ support a then Pi.single (removeIndex i a) 1 else 0 := by
  change evaluate (translate i (evaluate (Pi.single a 1)) -
    evaluate (Pi.single a 1)) = _
  rw [evaluate_basis, translate_sub_monomial]
  split <;> simp only [evaluate_monomial, map_zero]

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
