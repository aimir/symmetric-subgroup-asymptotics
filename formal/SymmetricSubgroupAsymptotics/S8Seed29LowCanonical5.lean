import SymmetricSubgroupAsymptotics.S8Seed29LowModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop15CatalogueBinding

/-! One actual canonical point-action binding for a low8T29 overgroup.
The displayed point permutation and both ordinary-word inclusions are
checked; no order recognition or abstract-isomorphism transport is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29LowCanonical5
open S8Seed29LeftCosets

def conjugator : Ambient where
  toFun := ![0, 1, 5, 2, 6, 3, 7, 4]
  invFun := ![0, 1, 3, 5, 7, 2, 4, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    (S8Seed29LowModels.generators 5) PrimitiveAffineEightTop15CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.mul (.generator 2) (.generator 3)) (.mul (.generator 4) (.generator 3))), (.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.mul (.generator 1) (.generator 2)), (.mul (.generator 3) (.mul (.generator 1) (.generator 4))), (.mul (.mul (.generator 0) (.generator 4)) (.mul (.generator 0) (.generator 4)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 2) (.generator 3)), (.mul (.generator 1) (.generator 3)), (.generator 1), (.mul (.generator 2) (.mul (.inv (.generator 4)) (.generator 0))), (.mul (.mul (.generator 0) (.inv (.generator 4))) (.mul (.generator 3) (.inv (.generator 4))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : MulAut.conj conjugator • S8Seed29LowModels.rows 5 =
    PrimitiveAffineEightTop15CatalogueBinding.catalogueAction := by
  change (S8Seed29LowModels.rows 5).map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop15CatalogueBinding.catalogueGenerators)
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed29LowCanonical5
end
