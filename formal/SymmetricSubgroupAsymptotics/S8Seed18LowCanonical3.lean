import SymmetricSubgroupAsymptotics.S8Seed18LowModels
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop3CatalogueBinding

/-! One actual canonical point-action binding for a low8T18 overgroup.
The displayed point permutation and both ordinary-word inclusions are
checked; no order recognition or abstract-isomorphism transport is used. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed18LowCanonical3
open S8Seed18LeftCosets

def conjugator : Ambient where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    (S8Seed18LowModels.generators 3) PrimitiveAffineEightTop3CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![(.mul (.inv (.generator 3)) (.generator 2)), (.generator 0), (.generator 1), (.generator 2), (.mul (.inv (.generator 3)) (.mul (.generator 4) (.generator 3))), (.generator 4)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 1), (.generator 2), (.generator 3), (.mul (.generator 3) (.inv (.generator 0))), (.generator 5)]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem exact_eq : MulAut.conj conjugator • S8Seed18LowModels.rows 3 =
    PrimitiveAffineEightTop3CatalogueBinding.catalogueAction := by
  change (S8Seed18LowModels.rows 3).map (MulAut.conj conjugator).toMonoidHom =
    Subgroup.closure (Set.range PrimitiveAffineEightTop3CatalogueBinding.catalogueGenerators)
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.S8Seed18LowCanonical3
end
