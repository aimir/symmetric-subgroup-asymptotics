import SymmetricSubgroupAsymptotics.BinaryBooleanFourDerivativeWords

/-! Derivative words require only genuine leading derivatives. Exact
pure translation identities are unnecessary; triangular action errors
may remain in every original intermediate vector. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth
variable {A M : Type} [Ring A] [AddCommGroup M] [Module A M] [Module (ZMod 2) M]

theorem exists_operator_leading_subset_of_leading_derivatives
    (C : M →ₗ[ZMod 2] V)
    (hderivative : ∀ (i : Fin 4) (z : M) (a : Fin 16),
      FiniteRowLeadingWeight.HasLeading (C z) a → i ∈ support a →
      ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • z)) (removeIndex i a))
    (v : M) (a b : Fin 16) (hv : FiniteRowLeadingWeight.HasLeading (C v) a)
    (hba : support b ⊆ support a) :
    ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) b := by
  apply ModuleLeadingOperatorWords.exists_operator_of_run derivativeStep
    (fun z a => FiniteRowLeadingWeight.HasLeading (C z) a) _
    (derivativePath a b) a b (derivativePath_valid a b hba) v hv
  intro i a b hab z hz
  change (if i ∈ support a then some (removeIndex i a) else none) = some b at hab
  split_ifs at hab with hi
  have he : removeIndex i a = b := Option.some.inj hab
  subst b
  exact hderivative i z a hz hi

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
