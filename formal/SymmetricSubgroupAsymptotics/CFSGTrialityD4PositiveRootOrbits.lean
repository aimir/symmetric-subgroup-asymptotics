import SymmetricSubgroupAsymptotics.CFSGTrialityD4NormTwo
import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramRoots
import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams

/-! Literal positive D4 triality root orbits. Each displayed vector is
proved norm two and positive. The three triples are orthogonal and are
cycled by the actual Cartan permutation; the three long roots are fixed.
Exhaustiveness of this list is a separate subsequent theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootOrbits
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoCartanDiagramRoots
open CFSGSerreDiagram

theorem cartan_eq : CartanMatrix.D 4 =
    !![(2 : ℤ),-1,0,0; -1,2,-1,-1; 0,-1,2,0; 0,-1,0,2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem triality_symm_apply (i : Fin 4) :
    trialityPermutation.symm i = ![3,1,0,2] i := by
  apply trialityPermutation.injective
  rw [Equiv.apply_symm_apply]
  change i = CFSG.Models.triality (![3,1,0,2] i)
  fin_cases i <;> decide

def shortCoordinates : Fin 3→Fin 3→Fin 4→ℤ:=![
  ![![1,0,0,0],![0,0,1,0],![0,0,0,1]],
  ![![1,1,0,0],![0,1,1,0],![0,1,0,1]],
  ![![1,1,1,0],![0,1,1,1],![1,1,0,1]]]

def longCoordinates : Fin 3→Fin 4→ℤ:=![![0,1,0,0],![1,1,1,1],![1,2,1,1]]

theorem short_norm (s k : Fin 3) :
    integerPairing (CartanMatrix.D 4) (shortCoordinates s k) (shortCoordinates s k)=2 := by
  fin_cases s <;> fin_cases k <;>
    norm_num [shortCoordinates,integerPairing,Matrix.toBilin'_apply,Matrix.mulVec,
      dotProduct,Fin.sum_univ_succ,cartan_eq]

theorem long_norm (s : Fin 3) :
    integerPairing (CartanMatrix.D 4) (longCoordinates s) (longCoordinates s)=2 := by
  fin_cases s <;>
    norm_num [longCoordinates,integerPairing,Matrix.toBilin'_apply,Matrix.mulVec,
      dotProduct,Fin.sum_univ_succ,cartan_eq]

def shortRoot (s k : Fin 3) : Roots (CartanMatrix.D 4):=⟨shortCoordinates s k,short_norm s k⟩
def longRoot (s : Fin 3) : Roots (CartanMatrix.D 4):=⟨longCoordinates s,long_norm s⟩

theorem short_positive (s k : Fin 3) (i : Fin 4) : 0≤(shortRoot s k).val i := by
  fin_cases s <;> fin_cases k <;> fin_cases i <;> decide

theorem long_positive (s : Fin 3) (i : Fin 4) : 0≤(longRoot s).val i := by
  fin_cases s <;> fin_cases i <;> decide

theorem short_orthogonal (s k l : Fin 3) (hkl : k≠l) :
    integerPairing (CartanMatrix.D 4) (shortRoot s k).val (shortRoot s l).val=0 := by
  fin_cases s <;> fin_cases k <;> fin_cases l <;>
    norm_num [shortRoot,shortCoordinates,integerPairing,Matrix.toBilin'_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,cartan_eq] at *

def cycle : Fin 3→Fin 3:=![1,2,0]

theorem short_triality (s k : Fin 3) :
    rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves (shortRoot s k)=
      shortRoot s (cycle k) := by
  apply Subtype.ext
  funext i
  change shortCoordinates s k (trialityPermutation.symm i)=shortCoordinates s (cycle k) i
  rw [triality_symm_apply]
  fin_cases s <;> fin_cases k <;> fin_cases i <;> decide

theorem long_triality (s : Fin 3) :
    rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves (longRoot s)=
      longRoot s := by
  apply Subtype.ext
  funext i
  change longCoordinates s (trialityPermutation.symm i)=longCoordinates s i
  rw [triality_symm_apply]
  fin_cases s <;> fin_cases i <;> decide

end SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootOrbits
