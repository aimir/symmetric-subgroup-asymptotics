import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveRootUnits
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! A literal element of the folded F4 positive subgroup has all six
ambient E6 simple leading coordinates equal to one. This is an actual
root-unit word, over every field, not a regularity premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RegularPositive
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckPositivePGroup

abbrev E6Positive (K : Type) [Field K] :=
  rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K false

def regularPositive (K : Type) [Field K] : E6Positive K :=
  positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 0 1 *
    positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 5 1 *
    positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 2 1 *
    positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 4 1 *
    positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 3 1 *
    positiveRoot CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K 1 1

def foldedRegular (K : Type) [Field K] : (Matrix Index Index K)ˣ :=
  canonicalRoot realizationData K false 0 1*canonicalRoot realizationData K false 1 1*
    canonicalRoot realizationData K false 2 1*canonicalRoot realizationData K false 3 1

theorem regularPositive_val (K : Type) [Field K] :
    (regularPositive K).val=foldedRegular K := by
  simp only [foldedRegular,folded_positive_root]
  change canonicalRoot e6Data K false 0 1*canonicalRoot e6Data K false 5 1*
      canonicalRoot e6Data K false 2 1*canonicalRoot e6Data K false 4 1*
      canonicalRoot e6Data K false 3 1*canonicalRoot e6Data K false 1 1=
    (canonicalRoot e6Data K false 0 1*canonicalRoot e6Data K false 5 1)*
      (canonicalRoot e6Data K false 2 1*canonicalRoot e6Data K false 4 1)*
      canonicalRoot e6Data K false 3 1*canonicalRoot e6Data K false 1 1
  simp only [mul_assoc]

theorem foldedRegular_mem (K : Type) [Field K] :
    foldedRegular K∈canonicalElementaryGroup realizationData K := by
  have hroot (i : Fin 4) : canonicalRoot realizationData K false i 1∈
      canonicalElementaryGroup realizationData K :=
    Subgroup.subset_closure ⟨false,i,1,rfl⟩
  exact (canonicalElementaryGroup realizationData K).mul_mem
    ((canonicalElementaryGroup realizationData K).mul_mem
      ((canonicalElementaryGroup realizationData K).mul_mem (hroot 0) (hroot 1)) (hroot 2)) (hroot 3)

theorem regularPositive_leading (K : Type) [Field K] (i : Fin 6) :
    leadingCoordinates CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (regularPositive K).val i=1 := by
  change (leadingHom CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (regularPositive K)).toAdd i=1
  simp only [regularPositive,map_mul,leadingHom_positiveRoot]
  change ((Pi.single 0 (1:K)+Pi.single 5 1+Pi.single 2 1+
    Pi.single 4 1+Pi.single 3 1+Pi.single 1 1 : Fin 6→K) i)=1
  fin_cases i <;> simp

theorem foldedRegular_leading_ne_zero (K : Type) [Field K] (i : Fin 6) :
    leadingCoordinates CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (foldedRegular K) i≠0 := by
  rw [←regularPositive_val,regularPositive_leading]
  exact one_ne_zero

end SymmetricSubgroupAsymptotics.CFSGFFourE6RegularPositive
