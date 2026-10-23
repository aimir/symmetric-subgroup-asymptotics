import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootOrbits
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree

/-! The two relative triality reflection words reach every displayed
positive root orbit. Computation is on the original integer lattice and
is identified with the actual based root-pairing word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4RelativeRootWords
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4NormTwo
open CFSGNormTwoGeckWeylWordDegree

def latticeStep (i : Fin 4) (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  x - integerPairing (CartanMatrix.D 4) x (Pi.single i (1 : ℤ)) • Pi.single i (1 : ℤ)

def latticeWord : List (Fin 4) → (Fin 4 → ℤ) → (Fin 4 → ℤ)
  | [], x => x
  | i :: w, x => latticeStep i (latticeWord w x)

def rootWord (w : List (Fin 4)) (k : Roots (CartanMatrix.D 4)) :
    Roots (CartanMatrix.D 4) :=
  wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index w k

theorem rootWord_val (w : List (Fin 4)) (k : Roots (CartanMatrix.D 4)) :
    (rootWord w k).val = latticeWord w k.val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (rootWord w k).val -
      integerPairing (CartanMatrix.D 4) (rootWord w k).val
        (Pi.single i (1 : ℤ)) • Pi.single i (1 : ℤ) = _
    rw [ih]
    rfl

theorem short_middle_lattice (k : Fin 3) :
    latticeWord [1] (shortCoordinates 0 k) = shortCoordinates 1 k := by
  funext j
  fin_cases k <;> fin_cases j <;> decide

theorem short_top_lattice (k : Fin 3) :
    latticeWord [0,2,3,1] (shortCoordinates 0 k) = shortCoordinates 2 (cycle k) := by
  funext j
  fin_cases k <;> fin_cases j <;> decide

theorem long_middle_lattice :
    latticeWord [0,2,3] (longCoordinates 0) = longCoordinates 1 := by
  funext j
  fin_cases j <;> decide

theorem long_top_lattice :
    latticeWord [1,0,2,3] (longCoordinates 0) = longCoordinates 2 := by
  funext j
  fin_cases j <;> decide

theorem short_middle (k : Fin 3) : rootWord [1] (shortRoot 0 k) = shortRoot 1 k := by
  apply Subtype.ext
  rw [rootWord_val]
  exact short_middle_lattice k

theorem short_top (k : Fin 3) :
    rootWord [0,2,3,1] (shortRoot 0 k) = shortRoot 2 (cycle k) := by
  apply Subtype.ext
  rw [rootWord_val]
  exact short_top_lattice k

theorem long_middle : rootWord [0,2,3] (longRoot 0) = longRoot 1 := by
  apply Subtype.ext
  rw [rootWord_val]
  exact long_middle_lattice

theorem long_top : rootWord [1,0,2,3] (longRoot 0) = longRoot 2 := by
  apply Subtype.ext
  rw [rootWord_val]
  exact long_top_lattice

end SymmetricSubgroupAsymptotics.CFSGTrialityD4RelativeRootWords
