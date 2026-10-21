import SymmetricSubgroupAsymptotics.BinaryBooleanFourTriangularDifferenceColumns
import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingDerivativeWords

/-! Polynomial coordinates of the same original triangular action.
Selected derivatives are supplied by genuine original group elements;
the formula retains all higher-coordinate errors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTriangularPointCoordinates
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {G X : Type} [Group G] [MulAction G X]
    (T : BinaryTriangularPointCoordinates G X 4)

def polynomialCoordinates : (X → ZMod 2) ≃ₗ[ZMod 2] V :=
  (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) T.booleanPointLabels.symm).trans coordinates

theorem polynomialCoordinates_actual_difference (g : G) (f : X → ZMod 2) :
    T.polynomialCoordinates
      (permutationFunctionRepresentation (ZMod 2) G X g⁻¹ f - f) =
      permutationDifference (T.actualBooleanPermutation g).symm (T.polynomialCoordinates f) := by
  change evaluate (fun j => f ((g⁻¹)⁻¹ • T.booleanPointLabels.symm j) -
    f (T.booleanPointLabels.symm j)) =
      permutationDifference (T.actualBooleanPermutation g).symm
        (evaluate (fun j => f (T.booleanPointLabels.symm j)))
  rw [permutationDifference_evaluate]
  refine congrArg (fun z : V => evaluate z) (funext fun j => ?_)
  change f ((g⁻¹)⁻¹ • T.booleanPointLabels.symm j) - f (T.booleanPointLabels.symm j) =
    f (T.booleanPointLabels.symm (T.booleanPointLabels (g • T.booleanPointLabels.symm j))) -
      f (T.booleanPointLabels.symm j)
  rw [inv_inv, Equiv.symm_apply_apply]

def subrepresentationCoordinates
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X)) :
    W.toSubmodule →ₗ[ZMod 2] V :=
  T.polynomialCoordinates.toLinearMap.comp W.toSubmodule.subtype

theorem subrepresentationCoordinates_injective
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X)) :
    Function.Injective (T.subrepresentationCoordinates W) := by
  intro a b hab
  apply Subtype.ext
  exact T.polynomialCoordinates.injective hab

theorem actual_leading_derivative
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (i : Fin 4) (v : W.toSubmodule) (a : Fin 16)
    (hv : FiniteRowLeadingWeight.HasLeading (T.subrepresentationCoordinates W v) a)
    (hia : i ∈ support a) :
    ∃ g : G, FiniteRowLeadingWeight.HasLeading
      (T.subrepresentationCoordinates W (W.toRepresentation g v - v)) (removeIndex i a) := by
  obtain ⟨g, hg⟩ := T.exists_actualBooleanPermutation_flip i
  refine ⟨g⁻¹, ?_⟩
  have he : T.subrepresentationCoordinates W (W.toRepresentation g⁻¹ v - v) =
      permutationDifference (T.actualBooleanPermutation g).symm
        (T.subrepresentationCoordinates W v) :=
    T.polynomialCoordinates_actual_difference g v.val
  rw [he]
  exact triangular_permutation_difference_hasLeading (T.actualBooleanPermutation g)
    (T.actualBooleanPermutation_triangular g) i hg _ a hv hia

end SymmetricSubgroupAsymptotics.BinaryTriangularPointCoordinates
