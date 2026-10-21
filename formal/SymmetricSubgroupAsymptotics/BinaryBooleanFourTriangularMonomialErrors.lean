import SymmetricSubgroupAsymptotics.BinaryBooleanFourTriangularAction
import SymmetricSubgroupAsymptotics.BinaryBooleanFourBlockPolynomialErrors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! A highest-variable identity for actual triangular polynomial errors.
The product in the error term is pointwise on original Boolean functions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem variable_monomial : ∀ j : Fin 4,
    monomial (support (variableIndex j)) = bitValue j := by decide

private theorem derivative_union_parts : ∀ (i j : Fin 4) (a : Fin 16),
    i < j → a.val < 2 ^ j.val →
      (i ∈ support (unionIndex (variableIndex j) a) ↔ i ∈ support a) ∧
      (i ∈ support a → removeIndex i (unionIndex (variableIndex j) a) =
        unionIndex (variableIndex j) (removeIndex i a)) := by decide

theorem derivative_union_variable (i j : Fin 4) (a : Fin 16)
    (hij : i < j) (ha : a.val < 2 ^ j.val) :
    derivative i (Pi.single (unionIndex (variableIndex j) a) 1) =
      monomialMultiplier (variableIndex j) (derivative i (Pi.single a 1)) := by
  obtain ⟨hm, hr⟩ := derivative_union_parts i j a hij ha
  rw [derivative_basis, derivative_basis]
  by_cases hi : i ∈ support a
  · rw [if_pos hi, if_pos (hm.mpr hi), hr hi, monomialMultiplier_basis]
  · rw [if_neg hi, if_neg (fun h => hi (hm.mp h)), map_zero]

theorem monomialMultiplier_evaluate (b : Fin 16) (f : V) :
    monomialMultiplier b (evaluate f) = evaluate (monomial (support b) * f) := by
  change evaluate (monomial (support b) * evaluate (evaluate f)) = _
  rw [evaluate_involutive]

def triangularMonomialError (p : Equiv.Perm (Fin 16)) (i : Fin 4) (a : Fin 16) : V :=
  evaluate ((fun x => monomial (support a) (p x)) - monomial (support a)) -
    derivative i (Pi.single a 1)

theorem triangularMonomialError_union_variable
    (p : Equiv.Perm (Fin 16)) (i j : Fin 4) (a : Fin 16)
    (hij : i < j) (ha : a.val < 2 ^ j.val) :
    triangularMonomialError p i (unionIndex (variableIndex j) a) =
      monomialMultiplier (variableIndex j) (triangularMonomialError p i a) +
        evaluate ((fun x => bitValue j (p x) - bitValue j x) *
          (fun x => monomial (support a) (p x))) := by
  have hm : monomial (support (unionIndex (variableIndex j) a)) =
      bitValue j * monomial (support a) := by
    rw [support_unionIndex, ← monomial_mul, variable_monomial]
  have he : (fun x => monomial (support (unionIndex (variableIndex j) a)) (p x)) -
      monomial (support (unionIndex (variableIndex j) a)) =
      bitValue j * ((fun x => monomial (support a) (p x)) - monomial (support a)) +
        (fun x => bitValue j (p x) - bitValue j x) *
          (fun x => monomial (support a) (p x)) := by
    rw [hm]
    funext x
    change bitValue j (p x) * monomial (support a) (p x) -
        bitValue j x * monomial (support a) x = _
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
    ring
  unfold triangularMonomialError
  rw [he, map_add, derivative_union_variable i j a hij ha, map_sub,
    monomialMultiplier_evaluate, variable_monomial]
  abel

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
