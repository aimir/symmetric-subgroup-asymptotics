import SymmetricSubgroupAsymptotics.S8Seed18LowModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop4CatalogueBinding

/-! One actual canonical point-action binding for a low8T18 overgroup.
The displayed point permutation and both ordinary-word inclusions are
checked; no order recognition or abstract-isomorphism transport is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed18LowCanonical2
open S8Seed18LeftCosets

def conjugator : Ambient where
  toFun := ![0, 1, 2, 3, 4, 6, 5, 7]
  invFun := ![0, 1, 2, 3, 4, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    (S8Seed18LowModels.generators 2) PrimitiveAffineEightTop4CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.generator 2) (.mul (.generator 0) (.inv (.generator 1)))), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 0) (.generator 2))), (.mul (.mul (.generator 0) (.mul (.generator 2) (.generator 1))) (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 0) (.generator 1)))), (.generator 2), (.mul (.generator 2) (.mul (.generator 0) (.generator 2))), (.mul (.mul (.generator 2) (.generator 1)) (.mul (.generator 0) (.mul (.generator 2) (.generator 1))))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 1) (.generator 4)), (.mul (.generator 0) (.mul (.generator 3) (.generator 5))), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : MulAut.conj conjugator • S8Seed18LowModels.rows 2 =
    PrimitiveAffineEightTop4CatalogueBinding.catalogueAction := by
  change (S8Seed18LowModels.rows 2).map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop4CatalogueBinding.catalogueGenerators)
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed18LowCanonical2
end
