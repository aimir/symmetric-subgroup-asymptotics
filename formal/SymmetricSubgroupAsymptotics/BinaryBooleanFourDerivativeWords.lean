import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingDerivatives
import SymmetricSubgroupAsymptotics.ModuleLeadingOperatorWords

/-! Prescribed difference words remove any desired subset of four
variables. Only sixteen-by-sixteen leading labels are checked finitely. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth

def derivativeStep (i : Fin 4) (a : Fin 16) : Option (Fin 16) :=
  if i ∈ support a then some (removeIndex i a) else none

def derivativePath (a b : Fin 16) : List (Fin 4) :=
  (List.ofFn fun i : Fin 4 => i).filter (fun i => decide (i ∈ support a \ support b))

theorem derivativePath_valid : ∀ a b : Fin 16,
    support b ⊆ support a →
      ModuleLeadingOperatorWords.run derivativeStep (derivativePath a b) a = some b := by decide

variable {A M : Type} [Ring A] [AddCommGroup M] [Module A M]
    [Module (ZMod 2) M]

theorem exists_operator_leading_subset
    (C : M →ₗ[ZMod 2] V)
    (hderivative : ∀ i : Fin 4, ∀ v : M, ∃ r : A, C (r • v) = derivative i (C v))
    (v : M) (a b : Fin 16) (hv : FiniteRowLeadingWeight.HasLeading (C v) a)
    (hba : support b ⊆ support a) :
    ∃ r : A, FiniteRowLeadingWeight.HasLeading (C (r • v)) b := by
  apply ModuleLeadingOperatorWords.exists_operator_of_run derivativeStep
    (fun v a => FiniteRowLeadingWeight.HasLeading (C v) a) _
    (derivativePath a b) a b (derivativePath_valid a b hba) v hv
  intro i a b hab v hv
  change (if i ∈ support a then some (removeIndex i a) else none) = some b at hab
  split_ifs at hab with hi
  · have he : removeIndex i a = b := Option.some.inj hab
    subst b
    obtain ⟨r, hr⟩ := hderivative i v
    refine ⟨r, ?_⟩
    change FiniteRowLeadingWeight.HasLeading (C (r • v)) (removeIndex i a)
    rw [hr]
    exact derivative_hasLeading i a (C v) hv hi

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
