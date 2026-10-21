import SymmetricSubgroupAsymptotics.S8Seed29LowModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop20CatalogueBinding

/-! One actual canonical point-action binding for a low8T29 overgroup.
The displayed point permutation and both ordinary-word inclusions are
checked; no order recognition or abstract-isomorphism transport is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29LowCanonical1
open S8Seed29LeftCosets

def conjugator : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    (S8Seed29LowModels.generators 1) PrimitiveAffineEightTop20CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 1) (.generator 3)) (.mul (.generator 5) (.inv (.generator 3)))), (.generator 0), (.generator 1), (.generator 2), (.mul (.mul (.generator 3) (.generator 3)) (.mul (.generator 3) (.mul (.generator 5) (.generator 3)))), (.mul (.mul (.inv (.generator 3)) (.inv (.generator 3))) (.mul (.generator 5) (.mul (.generator 3) (.generator 3))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 1), (.generator 2), (.generator 3), (.mul (.mul (.generator 4) (.inv (.generator 0))) (.mul (.inv (.generator 4)) (.mul (.generator 0) (.generator 4)))), (.mul (.mul (.generator 4) (.mul (.generator 4) (.inv (.generator 0)))) (.mul (.mul (.generator 4) (.generator 5)) (.mul (.generator 0) (.generator 4)))), (.mul (.mul (.generator 0) (.mul (.generator 1) (.inv (.generator 4)))) (.mul (.generator 0) (.mul (.generator 4) (.generator 0))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : MulAut.conj conjugator • S8Seed29LowModels.rows 1 =
    PrimitiveAffineEightTop20CatalogueBinding.catalogueAction := by
  change (S8Seed29LowModels.rows 1).map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop20CatalogueBinding.catalogueGenerators)
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed29LowCanonical1
end
