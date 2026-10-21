import SymmetricSubgroupAsymptotics.BinaryPairPolynomialCoordinates

/-! Polynomial differences for any actual top permutation. The original
lift offset remains in an unrestricted lower-layer error map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryBooleanFourPolynomialCoordinates

def permutationDifference (p : Equiv.Perm (Fin 16)) : V →ₗ[ZMod 2] V :=
  evaluate.comp ((reindex p).toLinearMap.comp evaluate) - LinearMap.id

def permutationOffsetError (a : V) (p : Equiv.Perm (Fin 16)) : V →ₗ[ZMod 2] V :=
  evaluate.comp ((multiplyFunction a).comp ((reindex p).toLinearMap.comp evaluate))

theorem permutationDifference_evaluate (p : Equiv.Perm (Fin 16)) (v : V) :
    permutationDifference p (evaluate v) = evaluate (reindex p v - v) := by
  change evaluate (reindex p (evaluate (evaluate v))) - evaluate v = _
  rw [evaluate_involutive, map_sub]

theorem permutationOffsetError_evaluate (a : V) (p : Equiv.Perm (Fin 16)) (v : V) :
    permutationOffsetError a p (evaluate v) = evaluate (a * reindex p v) := by
  change evaluate (a * reindex p (evaluate (evaluate v))) = _
  rw [evaluate_involutive]

end BinaryBooleanFourPolynomialCoordinates

namespace BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 16))

theorem polynomialPairCoordinate_permutation_difference
    (e p : Equiv.Perm (Fin 16)) (u : U)
    (hu : ∀ j, (F.top u)⁻¹ (e.symm j) = e.symm (p.symm j))
    (f : X → ZMod 2) :
    F.polynomialPairCoordinateEquiv e
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) =
      (permutationDifference p (F.polynomialPairCoordinateEquiv e f).1 +
        permutationOffsetError (F.polynomialLiftOffset e u) p
          (F.polynomialPairCoordinateEquiv e f).2,
        permutationDifference p (F.polynomialPairCoordinateEquiv e f).2) := by
  let z : V := fun j => F.pairZeroRestriction f (e.symm j)
  let s : V := fun j => F.pairSum f (e.symm j)
  have hz : (fun j => F.pairZeroRestriction
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) (e.symm j)) =
      BinaryBooleanFourPolynomialCoordinates.reindex p z + F.polynomialLiftOffset e u *
        BinaryBooleanFourPolynomialCoordinates.reindex p s - z := by
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
      BinaryBooleanFourPolynomialCoordinates.reindex p s - s := by
    funext j
    rw [map_sub, hsum]
    simp only [Pi.sub_apply]
    rw [hu]
    rfl
  apply Prod.ext
  · change evaluate (fun j => F.pairZeroRestriction
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) (e.symm j)) =
      permutationDifference p (evaluate z) +
        permutationOffsetError (F.polynomialLiftOffset e u) p (evaluate s)
    rw [hz, permutationDifference_evaluate, permutationOffsetError_evaluate,
      map_sub, map_add, map_sub]
    abel
  · change evaluate (fun j => F.pairSum
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) (e.symm j)) =
      permutationDifference p (evaluate s)
    rw [hs, permutationDifference_evaluate]

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
