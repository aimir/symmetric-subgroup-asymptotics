import SymmetricSubgroupAsymptotics.CFSGOrthogonalA4RootPilot
import Mathlib.Data.Matrix.Cartan

/-! The displayed nodes 1,3,4,5 form an actual A4 principal chain
orthogonal to node zero in each pinned E Cartan matrix. Thus all three
original lattices contain ten explicitly distinct positive roots
orthogonal to the original zeroth simple root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalOrthogonalA4Roots
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGOrthogonalA4RootPilot
open CFSGNormTwoCoordinatePositiveRootGenerators

def E6Nodes : Fin 4↪Fin 6 := ⟨fun i=>![1,3,4,5] i,by decide⟩
def E7Nodes : Fin 4↪Fin 7 := ⟨fun i=>![1,3,4,5] i,by decide⟩
def E8Nodes : Fin 4↪Fin 8 := ⟨fun i=>![1,3,4,5] i,by decide⟩

theorem E6_chain (i j : Fin 4) : CartanMatrix.E₆ (E6Nodes i) (E6Nodes j)=chainGram i j := by
  fin_cases i <;> fin_cases j <;> decide
theorem E7_chain (i j : Fin 4) : CartanMatrix.E₇ (E7Nodes i) (E7Nodes j)=chainGram i j := by
  fin_cases i <;> fin_cases j <;> decide
theorem E8_chain (i j : Fin 4) : CartanMatrix.E₈ (E8Nodes i) (E8Nodes j)=chainGram i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem E6_orthogonal (i : Fin 4) : CartanMatrix.E₆ (E6Nodes i) 0=0 := by
  fin_cases i <;> decide
theorem E7_orthogonal (i : Fin 4) : CartanMatrix.E₇ (E7Nodes i) 0=0 := by
  fin_cases i <;> decide
theorem E8_orthogonal (i : Fin 4) : CartanMatrix.E₈ (E8Nodes i) 0=0 := by
  fin_cases i <;> decide

theorem E6_ten_positive_orthogonal :
    ∃f : Fin 10→PositiveRoot CartanMatrix.E₆,Function.Injective f ∧
      ∀t,integerPairing CartanMatrix.E₆ (f t).val.val (Pi.single 0 (1:ℤ) : Fin 6→ℤ)=0 := by
  exact ⟨positiveRoots CartanMatrix.E₆ E6Nodes E6_chain,
    positiveRoots_injective CartanMatrix.E₆ E6Nodes E6_chain,
    vector_orthogonal CartanMatrix.E₆ E6Nodes 0 E6_orthogonal⟩

theorem E7_ten_positive_orthogonal :
    ∃f : Fin 10→PositiveRoot CartanMatrix.E₇,Function.Injective f ∧
      ∀t,integerPairing CartanMatrix.E₇ (f t).val.val (Pi.single 0 (1:ℤ) : Fin 7→ℤ)=0 := by
  exact ⟨positiveRoots CartanMatrix.E₇ E7Nodes E7_chain,
    positiveRoots_injective CartanMatrix.E₇ E7Nodes E7_chain,
    vector_orthogonal CartanMatrix.E₇ E7Nodes 0 E7_orthogonal⟩

theorem E8_ten_positive_orthogonal :
    ∃f : Fin 10→PositiveRoot CartanMatrix.E₈,Function.Injective f ∧
      ∀t,integerPairing CartanMatrix.E₈ (f t).val.val (Pi.single 0 (1:ℤ) : Fin 8→ℤ)=0 := by
  exact ⟨positiveRoots CartanMatrix.E₈ E8Nodes E8_chain,
    positiveRoots_injective CartanMatrix.E₈ E8Nodes E8_chain,
    vector_orthogonal CartanMatrix.E₈ E8Nodes 0 E8_orthogonal⟩

end SymmetricSubgroupAsymptotics.CFSGExceptionalOrthogonalA4Roots
