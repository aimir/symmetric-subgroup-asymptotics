import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixData
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Selected rank-two natural Serre-A realization

This small pilot checks all six families of the ORIGINAL rational A2 Serre
relations on explicit three-dimensional matrices. Entrywise arithmetic
only evaluates the four pairs of nodes in fixed 3-by-3 matrix identities. The resulting
integral square-zero data uses the shared divided-power/tensor descent.
No unitary-model equivalence or faithfulness assertion is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices

theorem a2_HH (i j : Fin 2) : ⁅cartan ℚ 2 i, cartan ℚ 2 j⁆ = 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [CartanMatrix.A, cartan, positive, negative, Ring.lie_def, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.single, Matrix.ofNat_apply, Fin.sum_univ_succ] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Matrix.ofNat_apply]

theorem a2_EF (i j : Fin 2) :
    ⁅positive ℚ 2 i, negative ℚ 2 j⁆ = if i = j then cartan ℚ 2 i else 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [CartanMatrix.A, cartan, positive, negative, Ring.lie_def, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.single, Matrix.ofNat_apply, Fin.sum_univ_succ] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Matrix.ofNat_apply]

theorem a2_HE (i j : Fin 2) :
    ⁅cartan ℚ 2 i, positive ℚ 2 j⁆ = CartanMatrix.A 2 i j • positive ℚ 2 j := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [CartanMatrix.A, cartan, positive, negative, Ring.lie_def, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.single, Matrix.ofNat_apply, Fin.sum_univ_succ] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Matrix.ofNat_apply]

theorem a2_HF (i j : Fin 2) :
    ⁅cartan ℚ 2 i, negative ℚ 2 j⁆ = -(CartanMatrix.A 2 i j • negative ℚ 2 j) := by
  fin_cases i <;> fin_cases j
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [CartanMatrix.A, cartan, positive, negative, Ring.lie_def, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.single, Matrix.ofNat_apply, Fin.sum_univ_succ] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Matrix.ofNat_apply]

theorem a2_EE (i j : Fin 2) :
    (LieAlgebra.ad ℚ (Mat ℚ 2) (positive ℚ 2 i) ^ (-CartanMatrix.A 2 i j).toNat)
      ⁅positive ℚ 2 i, positive ℚ 2 j⁆ = 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [CartanMatrix.A, LieAlgebra.ad_apply]
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [CartanMatrix.A, cartan, positive, negative, Ring.lie_def, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.single, Matrix.ofNat_apply, Fin.sum_univ_succ] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Matrix.ofNat_apply]

theorem a2_FF (i j : Fin 2) :
    (LieAlgebra.ad ℚ (Mat ℚ 2) (negative ℚ 2 i) ^ (-CartanMatrix.A 2 i j).toNat)
      ⁅negative ℚ 2 i, negative ℚ 2 j⁆ = 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [CartanMatrix.A, LieAlgebra.ad_apply]
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [CartanMatrix.A, cartan, positive, negative, Ring.lie_def, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.single, Matrix.ofNat_apply, Fin.sum_univ_succ] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Matrix.ofNat_apply]

def rationalNaturalA2 : CFSG.Models.Chevalley.RationalLie (CartanMatrix.A 2) →ₗ⁅ℚ⁆ Mat ℚ 2 :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    (cartan ℚ 2) (positive ℚ 2) (negative ℚ 2) (CartanMatrix.A 2)
    a2_HH a2_EF a2_HE a2_HF a2_EE a2_FF

@[simp] theorem rationalNaturalA2_H (i : Fin 2) :
    rationalNaturalA2 (CFSG.Models.Chevalley.generator (CartanMatrix.A 2)
      (CartanMatrix.Generators.H i)) = cartan ℚ 2 i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rationalNaturalA2_E (i : Fin 2) :
    rationalNaturalA2 (CFSG.Models.Chevalley.generator (CartanMatrix.A 2)
      (CartanMatrix.Generators.E i)) = positive ℚ 2 i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rationalNaturalA2_F (i : Fin 2) :
    rationalNaturalA2 (CFSG.Models.Chevalley.generator (CartanMatrix.A 2)
      (CartanMatrix.Generators.F i)) = negative ℚ 2 i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

def integerGenerator (r : ℕ) : CartanMatrix.Generators (Fin r) → Mat ℤ r
  | .H i => cartan ℤ r i
  | .E i => positive ℤ r i
  | .F i => negative ℤ r i

def realizationDataA2 : CFSGSerreSquareZeroMatrix.Data (CartanMatrix.A 2) (Fin 3) where
  rational := rationalNaturalA2
  integerGenerator := integerGenerator 2
  generator_cast := by
    intro g
    cases g with
    | H i => simpa only [integerGenerator, rationalNaturalA2_H] using
        map_cartan ℤ 2 (Int.castRingHom ℚ) i
    | E i => simpa only [integerGenerator, rationalNaturalA2_E] using
        map_positive ℤ 2 (Int.castRingHom ℚ) i
    | F i => simpa only [integerGenerator, rationalNaturalA2_F] using
        map_negative ℤ 2 (Int.castRingHom ℚ) i
  root_square_zero := by
    intro neg i
    cases neg
    · exact positive_sq_zero ℤ 2 i
    · exact negative_sq_zero ℤ 2 i

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
