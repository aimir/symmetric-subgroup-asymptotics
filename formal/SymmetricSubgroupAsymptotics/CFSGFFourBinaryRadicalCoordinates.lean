import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergStableRootFamilies
import SymmetricSubgroupAsymptotics.CFSGHeisenbergCoordinateGroup
import Mathlib.Algebra.CharP.Two

/-! The literal diagram-fixed ten-coordinate array has four singleton
coordinates and three paired coordinates. In characteristic two the
paired contributions to the Heisenberg cocycle cancel. Thus the paired
coordinates are genuine radical directions, not three more symplectic
pairs. This is only a coordinate pilot; no Levi orbit/index is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryRadicalCoordinates
open CFSGHeisenbergCoordinateGroup
open CFSGTwistedE6HeisenbergStableRootFamilies
variable {K : Type*}

def assemble (a : Fin 4 → K) (u : Fin 3 → K) : Fin 10 → K :=
  ![a 0, a 1, u 0, u 1, u 0, a 2, u 2, a 3, u 2, u 1]

def singleCoordinates (v : Fin 10 → K) : Fin 4 → K := ![v 0, v 1, v 5, v 7]
def pairCoordinates (v : Fin 10 → K) : Fin 3 → K := ![v 2, v 3, v 6]

theorem singleCoordinates_assemble (a : Fin 4 → K) (u : Fin 3 → K) :
    singleCoordinates (assemble a u) = a := by
  funext i
  fin_cases i <;> rfl

theorem pairCoordinates_assemble (a : Fin 4 → K) (u : Fin 3 → K) :
    pairCoordinates (assemble a u) = u := by
  funext i
  fin_cases i <;> rfl

theorem assemble_injective : Function.Injective
    (fun p : (Fin 4 → K) × (Fin 3 → K) => assemble p.1 p.2) := by
  intro p q he
  apply Prod.ext
  · have hh := congrArg singleCoordinates he
    simpa only [singleCoordinates_assemble] using hh
  · have hh := congrArg pairCoordinates he
    simpa only [pairCoordinates_assemble] using hh

theorem assemble_partner (a : Fin 4 → K) (u : Fin 3 → K) (i : Fin 10) :
    assemble a u (partner i) = assemble a u i := by
  fin_cases i <;> rfl

theorem assemble_dot [CommRing K] [CharP K 2]
    (b a : Fin 4 → K) (v u : Fin 3 → K) :
    dot (assemble b v) (assemble a u) = dot b a := by
  have he : dot (assemble b v) (assemble a u) =
      dot b a + 2 * (v 0 * u 0 + v 1 * u 1 + v 2 * u 2) := by
    simp only [dot, Fin.sum_univ_succ, assemble, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    norm_num
    rw [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 by decide]
    ring
  rw [he, CharTwo.two_eq_zero, zero_mul, add_zero]

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryRadicalCoordinates
