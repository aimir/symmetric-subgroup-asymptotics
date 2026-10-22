import SymmetricSubgroupAsymptotics.CFSGExceptionalIntegralGram
import SymmetricSubgroupAsymptotics.CFSGIntegralGramRootFiniteness
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing

/-! Finite actual norm-two root types for the three pinned E Cartan matrices.
Only fixed rectangular Gram identities are computed; no root enumeration occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoFinite
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalIntegralGram CFSGExceptionalCartanPositiveDefinite

private def sixToEight (i : Fin 6) : Fin 8 := ⟨i.val,by omega⟩
private def sevenToEight (i : Fin 7) : Fin 8 := ⟨i.val,by omega⟩

def gramSix : Matrix (Fin 8) (Fin 6) ℤ := fun i j=>integerColumns i (sixToEight j)
def gramSeven : Matrix (Fin 8) (Fin 7) ℤ := fun i j=>integerColumns i (sevenToEight j)

theorem gramSix_identity : gramSix.transpose*gramSix=(4:ℤ) • CartanMatrix.E₆ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramSix,sixToEight,integerColumns,integerRows,CartanMatrix.E₆,
      Matrix.mul_apply,Fin.sum_univ_succ]

theorem gramSeven_identity : gramSeven.transpose*gramSeven=(4:ℤ) • CartanMatrix.E₇ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramSeven,sevenToEight,integerColumns,integerRows,CartanMatrix.E₇,
      Matrix.mul_apply,Fin.sum_univ_succ]

instance rootsE6_finite : Finite (Roots CartanMatrix.E₆) :=
  (CFSGIntegralGramRootFiniteness.finite_norm_two CartanMatrix.E₆ gramSix 4
    (by decide) gramSix_identity E6_positive_definite).to_subtype

instance rootsE7_finite : Finite (Roots CartanMatrix.E₇) :=
  (CFSGIntegralGramRootFiniteness.finite_norm_two CartanMatrix.E₇ gramSeven 4
    (by decide) gramSeven_identity E7_positive_definite).to_subtype

instance rootsE8_finite : Finite (Roots CartanMatrix.E₈) :=
  (CFSGIntegralGramRootFiniteness.finite_norm_two CartanMatrix.E₈ integerColumns 4
    (by decide) integerColumns_gram E8_positive_definite).to_subtype

end SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoFinite
