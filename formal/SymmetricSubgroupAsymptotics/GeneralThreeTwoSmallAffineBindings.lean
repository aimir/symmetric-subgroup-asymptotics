import SymmetricSubgroupAsymptotics.GeneralThreeTwoRowGenerators
import SymmetricSubgroupAsymptotics.GeneralThreeTwoPointAction
import SymmetricSubgroupAsymptotics.SmallAffineSoluble8Row1Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble8Row2Order
import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate

/-! Ordinary-word bindings of the three surviving actual matrix subgroups
to the fixed degree-eight affine complement representatives. Both small
point conjugators are actual linear maps. No order-only recognition is used. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoSmallAffineBindings

open GeneralThreeTwoPointAction GeneralThreeTwoMatrixRows

def pointGenerators (i : Fin 15) (j : Fin 3) : Equiv.Perm (Fin 8) :=
  action (GeneralThreeTwoRowGenerators.generators i j)

theorem action_rows (i : Fin 15) :
    (GeneralThreeTwoActualSubgroupCoverage.rows i).map action =
      Subgroup.closure (Set.range (pointGenerators i)) := by
  rw [GeneralThreeTwoRowGenerators.rows_eq_closure, MonoidHom.map_closure]
  exact congrArg Subgroup.closure
    (Set.range_comp' action (GeneralThreeTwoRowGenerators.generators i)).symm

/-- Retains the actual GL3 matrix, not only an arbitrary point permutation. -/
def sevenConjugator : GeneralThreeTwoMatrixEncoding.Ambient := matrixRows 7
def twentyOneConjugator : GeneralThreeTwoMatrixEncoding.Ambient := matrixRows 5

def sevenCertificate : FiniteGeneratorEquivWordCertificate
    (MulAut.conj (action sevenConjugator))
    (pointGenerators 4) SmallAffineSoluble8Row1Order.generators where
  forward := {
    words := ![.mul (.generator 0) (.mul (.generator 0) (.generator 0)), .one, .one]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![.mul (.inv (.generator 0)) (.inv (.generator 0))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

def twentyOneCertificate : FiniteGeneratorEquivWordCertificate
    (MulAut.conj (action twentyOneConjugator))
    (pointGenerators 14) SmallAffineSoluble8Row2Order.generators where
  forward := {
    words := ![.mul (.generator 0) (.generator 0),
      .mul (.inv (.generator 0)) (.generator 1), .one]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }
  backward := {
    words := ![.mul (.inv (.generator 0))
        (.mul (.inv (.generator 0)) (.inv (.generator 0))),
      .mul (.generator 1) (.mul (.generator 0) (.generator 0))]
    equations := by
      intro j
      fin_cases j <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel }

theorem seven_conjugate :
    MulAut.conj (action sevenConjugator) •
      (GeneralThreeTwoActualSubgroupCoverage.rows 4).map action =
        SmallAffineSoluble8Row1Order.R := by
  rw [action_rows]
  exact sevenCertificate.map_closure_eq

theorem twentyOne_conjugate :
    MulAut.conj (action twentyOneConjugator) •
      (GeneralThreeTwoActualSubgroupCoverage.rows 14).map action =
        SmallAffineSoluble8Row2Order.R := by
  rw [action_rows]
  exact twentyOneCertificate.map_closure_eq

private def fullCertificate : FiniteGeneratorWordCertificate
    GeneralThreeTwoMatrixEncoding.generators (GeneralThreeTwoRowGenerators.generators 7) where
  words := ![
    .mul (.generator 0) (.mul (.generator 0) (.mul (.generator 1)
      (.mul (.inv (.generator 0)) (.inv (.generator 0))))),
    .mul (.generator 0) (.mul (.generator 1) (.mul (.inv (.generator 0))
      (.mul (.inv (.generator 0)) (.mul (.inv (.generator 0))
        (.mul (.generator 1) (.mul (.generator 0) (.generator 1)))))))]
  equations := by
    intro j
    fin_cases j <;> apply Units.ext <;> decide +kernel

theorem full_row : GeneralThreeTwoActualSubgroupCoverage.rows 7 = ⊤ := by
  apply top_le_iff.mp
  rw [GeneralThreeTwoRowGenerators.rows_eq_closure,
    ← GeneralThreeTwoCayley.generated_eq_top]
  exact fullCertificate.closure_le

def sevenEquiv : GeneralThreeTwoActualSubgroupCoverage.rows 4 ≃*
    SmallAffineSoluble8Row1Order.R :=
  ((GeneralThreeTwoActualSubgroupCoverage.rows 4).equivMapOfInjective
    action action_injective).trans
    (((MulAut.conj (action sevenConjugator)).subgroupMap _).trans
      (MulEquiv.subgroupCongr seven_conjugate))

def twentyOneEquiv : GeneralThreeTwoActualSubgroupCoverage.rows 14 ≃*
    SmallAffineSoluble8Row2Order.R :=
  ((GeneralThreeTwoActualSubgroupCoverage.rows 14).equivMapOfInjective
    action action_injective).trans
    (((MulAut.conj (action twentyOneConjugator)).subgroupMap _).trans
      (MulEquiv.subgroupCongr twentyOne_conjugate))

def fullEquiv : GeneralThreeTwoActualSubgroupCoverage.rows 7 ≃*
    StandardThreeDimensionalLinearGroups.GeneralThree 2 :=
  (MulEquiv.subgroupCongr full_row).trans Subgroup.topEquiv

end SymmetricSubgroupAsymptotics.GeneralThreeTwoSmallAffineBindings

end
