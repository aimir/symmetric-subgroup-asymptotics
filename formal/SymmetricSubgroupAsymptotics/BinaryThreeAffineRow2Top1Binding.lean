import SymmetricSubgroupAsymptotics.BinaryThreeAffineRowGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop1CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One actual fixed affine row point binding, certified by ordinary words.
No finite-row completeness, primitive-action or numerical match is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryThreeAffineRow2Top1Binding
open BinaryThreeAffineRowActions

def conjugator : Ambient where
  toFun := ![0, 1, 5, 4, 2, 7, 3, 6]
  invFun := ![0, 1, 4, 6, 3, 2, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    (BinaryThreeAffineRowGenerators.generators 2) PrimitiveAffineEightTop1CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![.one, (.mul (.generator 0) (.generator 1)), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 2), (.generator 1), (.generator 0), (.mul (.generator 0) (.generator 2)), (.mul (.generator 1) (.generator 2)), (.mul (.generator 1) (.inv (.generator 3))), .one, .one]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 5), (.generator 4), (.generator 3), (.mul (.generator 1) (.inv (.generator 8)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator • rows 2 =
    PrimitiveAffineEightTop1CatalogueBinding.catalogueAction := by
  change (rows 2).map (MulAut.conj conjugator).toMonoidHom = _
  rw [BinaryThreeAffineRowGenerators.rows_eq_closure]
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.BinaryThreeAffineRow2Top1Binding
end
