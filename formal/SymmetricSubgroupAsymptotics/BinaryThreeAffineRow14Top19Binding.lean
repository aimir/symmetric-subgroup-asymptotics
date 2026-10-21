import SymmetricSubgroupAsymptotics.BinaryThreeAffineRowGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop19CatalogueBinding
import Mathlib.Tactic.FinCases

/-! One actual fixed affine row point binding, certified by ordinary words.
No finite-row completeness, primitive-action or numerical match is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryThreeAffineRow14Top19Binding
open BinaryThreeAffineRowActions

def conjugator : Ambient where
  toFun := ![0, 1, 2, 7, 3, 6, 5, 4]
  invFun := ![0, 1, 2, 4, 7, 6, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    (BinaryThreeAffineRowGenerators.generators 14) PrimitiveAffineEightTop19CatalogueBinding.catalogueGenerators where
  forward := {
    words := ![.one, (.mul (.generator 0) (.generator 1)), (.generator 1), (.generator 0), (.mul (.generator 0) (.generator 2)), (.mul (.generator 1) (.generator 2)), (.mul (.generator 0) (.mul (.generator 1) (.generator 2))), (.generator 2), (.mul (.generator 0) (.mul (.generator 1) (.generator 3))), (.mul (.generator 4) (.mul (.generator 2) (.inv (.generator 3)))), .one]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![(.generator 3), (.generator 2), (.generator 7), (.mul (.generator 1) (.generator 8)), (.mul (.generator 1) (.mul (.generator 9) (.generator 8)))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem canonical_conjugated : MulAut.conj conjugator • rows 14 =
    PrimitiveAffineEightTop19CatalogueBinding.catalogueAction := by
  change (rows 14).map (MulAut.conj conjugator).toMonoidHom = _
  rw [BinaryThreeAffineRowGenerators.rows_eq_closure]
  exact certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.BinaryThreeAffineRow14Top19Binding
end
