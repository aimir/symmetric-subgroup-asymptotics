import SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreRepresentation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-! Four folded generator relations, evaluated in the original D4 matrices.
In particular the Cartan table is G₂ itself, not its transpose. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
variable (R : Type*) [CommRing R]

@[simp] theorem negative_zero : negative R 0=
    CFSGOrthogonalDSerreMatrices.negative R 4 0+
      CFSGOrthogonalDSerreMatrices.negative R 4 2+
        CFSGOrthogonalDSerreMatrices.negative R 4 3 := by
  simp only [negative,positive_zero,outerPositive,Matrix.transpose_add,
    CFSGOrthogonalDSerreMatrices.negative]

@[simp] theorem negative_one : negative R 1=
    CFSGOrthogonalDSerreMatrices.negative R 4 1 := by
  simp only [negative,positive_one,CFSGOrthogonalDSerreMatrices.negative]

 theorem EF (i j : Fin 2) :
    ⁅positive R i,negative R j⁆=if i=j then cartan R i else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [positive,outerPositive,negative_zero,negative_one,cartan,
      add_lie,lie_add,CFSGOrthogonalDSerreMatrices.EF R 4 (by decide)]

 theorem cartan_cartan (i j : Fin 2) : ⁅cartan R i,cartan R j⁆=0 := by
  fin_cases i <;> fin_cases j <;>
    simp [cartan,add_lie,lie_add,
      CFSGOrthogonalDSerreMatrices.cartan_cartan R 4 (by decide)]

 theorem HE (i j : Fin 2) :
    ⁅cartan R i,positive R j⁆=CartanMatrix.G₂ i j • positive R j := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [cartan,positive,CartanMatrix.G₂]
    simp only [outerPositive,add_lie,lie_add,
      CFSGOrthogonalDSerreMatrices.HE R 4 (by decide)]
    norm_num [CartanMatrix.D,smul_add] <;> noncomm_ring <;> simp only [neg_one_smul,neg_neg,zero_add] <;> abel

 theorem HF (i j : Fin 2) :
    ⁅cartan R i,negative R j⁆= -(CartanMatrix.G₂ i j • negative R j) := by
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [cartan,negative_zero,negative_one,CartanMatrix.G₂]
    simp only [add_lie,lie_add,CFSGOrthogonalDSerreMatrices.HF R 4 (by decide)]
    norm_num [CartanMatrix.D,smul_add] <;> noncomm_ring <;> simp only [neg_one_smul,neg_neg,zero_add] <;> abel

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
