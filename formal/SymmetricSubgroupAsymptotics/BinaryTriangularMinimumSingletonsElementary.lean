import SymmetricSubgroupAsymptotics.BinaryTriangularPolynomialRepresentation
import SymmetricSubgroupAsymptotics.BinaryBooleanFourTriangularSingletonDifference
import SymmetricSubgroupAsymptotics.BinarySingletonMinimumGeneratorDisplacements
import SymmetricSubgroupAsymptotics.BinarySingletonLeadingPointSeparation
import SymmetricSubgroupAsymptotics.BinaryPointSeparatingConstantDisplacements

/-! The four-singleton minimum-generator exception forces the same
original point action to have exponent two. All differences and all
intermediate cancellation operators remain in the original module. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryTriangularPointCoordinates
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {G X : Type} [Group G] [MulAction G X]
    (T : BinaryTriangularPointCoordinates G X 4)

def subrepresentationModuleCoordinates
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X)) :
    W.toRepresentation.asModule →ₗ[ZMod 2] V :=
  (T.subrepresentationCoordinates W).comp W.toRepresentation.asModuleEquiv.toLinearMap

private theorem polynomialCoordinates_evaluate (f : X → ZMod 2) (x : X) :
    evaluate (T.polynomialCoordinates f) (T.booleanPointLabels x) = f x := by
  change evaluate (evaluate (fun j => f (T.booleanPointLabels.symm j)))
    (T.booleanPointLabels x) = f x
  rw [evaluate_involutive, Equiv.symm_apply_apply]

private theorem moduleCoordinates_difference
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (g : G) (v : W.toRepresentation.asModule) :
    T.subrepresentationModuleCoordinates W ((MonoidAlgebra.single g (1 : ZMod 2) - 1) • v) =
      permutationDifference (T.actualBooleanPermutation g⁻¹).symm
        (T.subrepresentationModuleCoordinates W v) := by
  change T.subrepresentationCoordinates W
    (W.toRepresentation.asAlgebraHom
      (MonoidAlgebra.single g (1 : ZMod 2) - 1)
      (W.toRepresentation.asModuleEquiv v)) = _
  rw [map_sub, Representation.asAlgebraHom_single, map_one, LinearMap.sub_apply,
    Module.End.one_apply, one_smul]
  have he := T.polynomialCoordinates_actual_difference g⁻¹
    (W.toRepresentation.asModuleEquiv v).val
  simpa only [inv_inv] using he

private theorem moduleCoordinates_original_difference
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (g : G) (v : W.toRepresentation.asModule) :
    T.subrepresentationModuleCoordinates W ((MonoidAlgebra.single g (1 : ZMod 2) - 1) • v) =
      T.polynomialCoordinates (fun x => (W.toRepresentation.asModuleEquiv v).val (g⁻¹ • x) -
        (W.toRepresentation.asModuleEquiv v).val x) := by
  change T.subrepresentationCoordinates W
    (W.toRepresentation.asAlgebraHom
      (MonoidAlgebra.single g (1 : ZMod 2) - 1)
      (W.toRepresentation.asModuleEquiv v)) = _
  rw [map_sub, Representation.asAlgebraHom_single, map_one, LinearMap.sub_apply,
    Module.End.one_apply, one_smul]
  rfl

theorem squaresActTrivially_of_minimum_singleton_generators
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (v : Fin 4 → W.toRepresentation.asModule)
    (hlead : ∀ i, FiniteRowLeadingWeight.HasLeading
      (T.subrepresentationModuleCoordinates W (v i)) (variableIndex i))
    (hnocollision : ∀ i j : Fin 4, i ≠ j → ∀ r : (ZMod 2)[G],
      ¬FiniteRowLeadingWeight.HasLeading
        (T.subrepresentationModuleCoordinates W (r • v i)) (variableIndex j)) :
    BinarySquareActionStructure.SquaresActTrivially (G := G) (X := X) := by
  letI : AddCommGroup W.toRepresentation.asModule :=
    inferInstanceAs (AddCommGroup W.toSubmodule)
  let E := T.subrepresentationModuleCoordinates W
  let delta : G → (ZMod 2)[G] := fun g => MonoidAlgebra.single g (1 : ZMod 2) - 1
  have hderivative : ∀ (i : Fin 4) (z : W.toRepresentation.asModule) (a : Fin 16),
      FiniteRowLeadingWeight.HasLeading (E z) a → i ∈ support a →
      ∃ r : (ZMod 2)[G], FiniteRowLeadingWeight.HasLeading (E (r • z)) (removeIndex i a) := by
    intro i z a hz hia
    obtain ⟨g, hg⟩ := T.exists_actualBooleanPermutation_flip i
    refine ⟨delta g⁻¹, ?_⟩
    rw [moduleCoordinates_difference]
    simpa only [inv_inv] using triangular_permutation_difference_hasLeading
      (T.actualBooleanPermutation g) (T.actualBooleanPermutation_triangular g) i hg (E z) a hz hia
  have htriangular : ∀ g i (a : Fin 16), variableIndex i ≤ a → E (delta g • v i) a = 0 := by
    intro g i a ha
    rw [moduleCoordinates_difference]
    exact triangular_singleton_difference_zero_above (T.actualBooleanPermutation g⁻¹)
      (T.actualBooleanPermutation_triangular g⁻¹) i (E (v i)) (hlead i) a ha
  have hconstant := singleton_minimum_generator_displacements_constant E v delta
    hnocollision hderivative htriangular
  let f : Fin 4 → X → ZMod 2 := fun i => (W.toRepresentation.asModuleEquiv (v i)).val
  have hpoint : Function.Injective (fun x : X => fun i : Fin 4 => f i x) := by
    intro x y he
    apply T.booleanPointLabels.injective
    apply singleton_leading_point_family_injective (fun i => E (v i)) hlead
    funext i
    change evaluate (T.polynomialCoordinates (f i)) (T.booleanPointLabels x) =
      evaluate (T.polynomialCoordinates (f i)) (T.booleanPointLabels y)
    rw [polynomialCoordinates_evaluate, polynomialCoordinates_evaluate]
    exact congrFun he i
  apply squaresActTrivially_of_pointSeparating_constant_displacements f hpoint
  intro g i x y
  have hz : ∀ a : Fin 16, 2 ^ (0 : Fin 5).val ≤ a.val → E (delta g⁻¹ • v i) a = 0 := by
    intro a ha
    norm_num only [Fin.val_zero,Nat.pow_zero] at ha
    exact hconstant g⁻¹ i a (by change 0 < a.val; omega)
  have hpref := prefix_evaluate_of_coefficients_zero (E (delta g⁻¹ • v i)) (0 : Fin 5) hz
  have heval : ∀ z : X, evaluate (E (delta g⁻¹ • v i)) (T.booleanPointLabels z) =
      f i (g • z) - f i z := by
    intro z
    have he : E (delta g⁻¹ • v i) =
        T.polynomialCoordinates (fun x => f i (g • x) - f i x) := by
      change T.subrepresentationModuleCoordinates W
        ((MonoidAlgebra.single g⁻¹ (1 : ZMod 2) - 1) • v i) = _
      rw [moduleCoordinates_original_difference]
      change T.polynomialCoordinates (fun x => f i ((g⁻¹)⁻¹ • x) - f i x) = _
      rw [inv_inv]
    rw [he, polynomialCoordinates_evaluate]
  rw [← heval x, ← heval y]
  apply hpref
  intro j hj
  exact False.elim (Nat.not_lt_zero j.val hj)

end SymmetricSubgroupAsymptotics.BinaryTriangularPointCoordinates
