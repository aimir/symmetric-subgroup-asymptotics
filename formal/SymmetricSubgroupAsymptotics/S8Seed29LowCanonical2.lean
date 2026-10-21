import SymmetricSubgroupAsymptotics.S8Seed29LowModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop23CatalogueBinding

/-! One actual canonical point-action binding for a low8T29 overgroup.
The displayed point permutation and both ordinary-word inclusions are
checked; no order recognition or abstract-isomorphism transport is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29LowCanonical2
open S8Seed29LeftCosets

def conjugator : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    (S8Seed29LowModels.generators 2) PrimitiveAffineEightTop23CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 0) (.mul (.generator 0) (.generator 0))) (.mul (.mul (.inv (.generator 1)) (.inv (.generator 0))) (.mul (.generator 1) (.inv (.generator 0))))), (.mul (.mul (.mul (.generator 0) (.mul (.generator 0) (.generator 0))) (.mul (.inv (.generator 1)) (.mul (.generator 0) (.inv (.generator 1))))) (.mul (.mul (.generator 0) (.mul (.generator 0) (.generator 0))) (.mul (.inv (.generator 1)) (.mul (.generator 0) (.inv (.generator 1)))))), (.mul (.mul (.mul (.generator 0) (.inv (.generator 1))) (.mul (.inv (.generator 0)) (.mul (.inv (.generator 1)) (.inv (.generator 0))))) (.mul (.mul (.inv (.generator 0)) (.mul (.generator 1) (.inv (.generator 0)))) (.mul (.inv (.generator 1)) (.mul (.inv (.generator 0)) (.generator 1))))), (.mul (.mul (.generator 0) (.mul (.generator 0) (.inv (.generator 1)))) (.mul (.generator 0) (.mul (.generator 0) (.inv (.generator 1))))), (.mul (.mul (.mul (.generator 0) (.inv (.generator 1))) (.mul (.generator 0) (.mul (.generator 0) (.generator 0)))) (.mul (.mul (.generator 1) (.mul (.inv (.generator 0)) (.inv (.generator 1)))) (.mul (.inv (.generator 0)) (.mul (.inv (.generator 0)) (.generator 1))))), (.mul (.mul (.mul (.generator 0) (.mul (.generator 0) (.inv (.generator 1)))) (.mul (.generator 0) (.mul (.generator 1) (.generator 0)))) (.mul (.mul (.generator 0) (.mul (.inv (.generator 1)) (.generator 0))) (.mul (.mul (.generator 0) (.generator 1)) (.mul (.generator 0) (.inv (.generator 1))))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.mul (.generator 1) (.generator 4)) (.mul (.generator 5) (.generator 0))), (.mul (.mul (.generator 1) (.mul (.inv (.generator 0)) (.inv (.generator 0)))) (.mul (.generator 4) (.mul (.generator 0) (.generator 1))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : MulAut.conj conjugator • S8Seed29LowModels.rows 2 =
    PrimitiveAffineEightTop23CatalogueBinding.catalogueAction := by
  change (S8Seed29LowModels.rows 2).map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop23CatalogueBinding.catalogueGenerators)
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed29LowCanonical2
end
