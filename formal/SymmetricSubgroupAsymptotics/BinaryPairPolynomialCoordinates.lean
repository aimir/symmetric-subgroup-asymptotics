import SymmetricSubgroupAsymptotics.BinaryBooleanFourTwoLayerLeading
import SymmetricSubgroupAsymptotics.BinarySplitAffineFunctionCoordinates
import Mathlib.Tactic.Abel

/-! Polynomial coordinates for an original outer binary-pair action.
The difference of a genuine top-translation lift and the identity has
the triangular form used by the leading proof, with its actual offset
retained as an unrestricted lower-error map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

def reindex (e : Equiv.Perm (Fin 16)) : V ≃ₗ[ZMod 2] V where
  toFun v := fun j => v (e.symm j)
  invFun v := fun j => v (e j)
  left_inv v := by funext j; simp only [Equiv.symm_apply_apply]
  right_inv v := by funext j; simp only [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def multiplyFunction (a : V) : V →ₗ[ZMod 2] V where
  toFun v := a * v
  map_add' v z := by funext j; exact mul_add _ _ _
  map_smul' c v := by
    funext j
    change a j * (c * v j) = c * (a j * v j)
    exact mul_left_comm _ _ _

def offsetError (a : V) (i : Fin 4) : V →ₗ[ZMod 2] V :=
  evaluate.comp ((multiplyFunction a).comp ((translate i).comp evaluate))

theorem derivative_evaluate (i : Fin 4) (v : V) :
    derivative i (evaluate v) = evaluate (translate i v - v) := by
  change evaluate (translate i (evaluate (evaluate v)) - evaluate (evaluate v)) = _
  rw [evaluate_involutive]

theorem offsetError_evaluate (a : V) (i : Fin 4) (v : V) :
    offsetError a i (evaluate v) = evaluate (a * translate i v) := by
  change evaluate (a * translate i (evaluate (evaluate v))) = _
  rw [evaluate_involutive]

end BinaryBooleanFourPolynomialCoordinates

namespace BinaryPairFrame

open BinaryBooleanFourPolynomialCoordinates
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 16))

def polynomialPairCoordinateEquiv (e : Equiv.Perm (Fin 16)) :
    (X → ZMod 2) ≃ₗ[ZMod 2] (V × V) :=
  F.pairLayerCoordinateEquiv.trans
    (((BinaryBooleanFourPolynomialCoordinates.reindex e).trans coordinates).prodCongr
      ((BinaryBooleanFourPolynomialCoordinates.reindex e).trans coordinates))

/-- This is the actual offset of the inverse lift at the same destination
point, expressed in the displayed Boolean point coordinates. -/
def polynomialLiftOffset (e : Equiv.Perm (Fin 16)) (u : U) : V :=
  fun j => F.offset u⁻¹ (e.symm j)

theorem polynomialPairCoordinate_difference
    (e : Equiv.Perm (Fin 16)) (u : U) (i : Fin 4)
    (hu : ∀ j, (F.top u)⁻¹ (e.symm j) = e.symm (flipIndex i j))
    (f : X → ZMod 2) :
    F.polynomialPairCoordinateEquiv e
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) =
      (derivative i (F.polynomialPairCoordinateEquiv e f).1 +
        offsetError (F.polynomialLiftOffset e u) i (F.polynomialPairCoordinateEquiv e f).2,
        derivative i (F.polynomialPairCoordinateEquiv e f).2) := by
  let z : V := fun j => F.pairZeroRestriction f (e.symm j)
  let s : V := fun j => F.pairSum f (e.symm j)
  have hz : (fun j => F.pairZeroRestriction
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) (e.symm j)) =
      translate i z + F.polynomialLiftOffset e u * translate i s - z := by
    funext j
    rw [map_sub, F.pairZeroRestriction_action]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    rw [hu]
    rfl
  have hsum := Representation.IntertwiningMap.isIntertwining _ _ F.pairSumIntertwiner u f
  change F.pairSum (permutationFunctionRepresentation (ZMod 2) U X u f) =
    (fun j => F.pairSum f ((F.top u)⁻¹ j)) at hsum
  have hs : (fun j => F.pairSum
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) (e.symm j)) =
      translate i s - s := by
    funext j
    rw [map_sub, hsum]
    simp only [Pi.sub_apply]
    rw [hu]
    rfl
  apply Prod.ext
  · change evaluate (fun j => F.pairZeroRestriction
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) (e.symm j)) =
      derivative i (evaluate z) + offsetError (F.polynomialLiftOffset e u) i (evaluate s)
    rw [hz, derivative_evaluate, offsetError_evaluate, map_sub, map_add, map_sub]
    abel
  · change evaluate (fun j => F.pairSum
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) (e.symm j)) =
      derivative i (evaluate s)
    rw [hs, derivative_evaluate]

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
