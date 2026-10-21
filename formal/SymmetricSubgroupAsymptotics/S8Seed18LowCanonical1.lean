import SymmetricSubgroupAsymptotics.S8Seed18LowModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop5CatalogueBinding

/-! One actual canonical point-action binding for a low8T18 overgroup.
The displayed point permutation and both ordinary-word inclusions are
checked; no order recognition or abstract-isomorphism transport is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed18LowCanonical1
open S8Seed18LeftCosets

def conjugator : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    (S8Seed18LowModels.generators 1) PrimitiveAffineEightTop5CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.inv (.generator 1)), (.mul (.mul (.mul (.generator 2) (.inv (.generator 1))) (.mul (.generator 0) (.generator 1))) (.mul (.mul (.generator 2) (.inv (.generator 1))) (.mul (.generator 0) (.generator 1)))), (.mul (.mul (.generator 0) (.generator 2)) (.mul (.generator 0) (.generator 2))), (.generator 2), (.mul (.mul (.generator 2) (.inv (.generator 1))) (.mul (.generator 0) (.mul (.generator 1) (.generator 2)))), (.mul (.generator 2) (.mul (.generator 0) (.generator 2)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.mul (.generator 2) (.generator 5)), (.inv (.generator 0)), (.generator 3)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : MulAut.conj conjugator • S8Seed18LowModels.rows 1 =
    PrimitiveAffineEightTop5CatalogueBinding.catalogueAction := by
  change (S8Seed18LowModels.rows 1).map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop5CatalogueBinding.catalogueGenerators)
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed18LowCanonical1
end
