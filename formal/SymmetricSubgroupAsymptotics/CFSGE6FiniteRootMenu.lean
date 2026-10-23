import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFiniteRootMenu
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! A literal reflection-stable menu for the pinned E6 integer lattice.
Negative-simple membership, reflection closure, and both menu sizes are
kernel-checked. Coverage is deduced from the root-word orbit theorem. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateFiniteRootMenu CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGExceptionalCartanPositiveDefinite

def menu : Finset (Fin 6→ℤ) := {
    ![-1,-2,-2,-3,-2,-1],
    ![-1,-1,-2,-3,-2,-1],
    ![-1,-1,-2,-2,-2,-1],
    ![-1,-1,-2,-2,-1,-1],
    ![-1,-1,-2,-2,-1,0],
    ![-1,-1,-1,-2,-2,-1],
    ![-1,-1,-1,-2,-1,-1],
    ![-1,-1,-1,-2,-1,0],
    ![-1,-1,-1,-1,-1,-1],
    ![-1,-1,-1,-1,-1,0],
    ![-1,-1,-1,-1,0,0],
    ![-1,0,-1,-1,-1,-1],
    ![-1,0,-1,-1,-1,0],
    ![-1,0,-1,-1,0,0],
    ![-1,0,-1,0,0,0],
    ![-1,0,0,0,0,0],
    ![0,-1,-1,-2,-2,-1],
    ![0,-1,-1,-2,-1,-1],
    ![0,-1,-1,-2,-1,0],
    ![0,-1,-1,-1,-1,-1],
    ![0,-1,-1,-1,-1,0],
    ![0,-1,-1,-1,0,0],
    ![0,-1,0,-1,-1,-1],
    ![0,-1,0,-1,-1,0],
    ![0,-1,0,-1,0,0],
    ![0,-1,0,0,0,0],
    ![0,0,-1,-1,-1,-1],
    ![0,0,-1,-1,-1,0],
    ![0,0,-1,-1,0,0],
    ![0,0,-1,0,0,0],
    ![0,0,0,-1,-1,-1],
    ![0,0,0,-1,-1,0],
    ![0,0,0,-1,0,0],
    ![0,0,0,0,-1,-1],
    ![0,0,0,0,-1,0],
    ![0,0,0,0,0,-1],
    ![0,0,0,0,0,1],
    ![0,0,0,0,1,0],
    ![0,0,0,0,1,1],
    ![0,0,0,1,0,0],
    ![0,0,0,1,1,0],
    ![0,0,0,1,1,1],
    ![0,0,1,0,0,0],
    ![0,0,1,1,0,0],
    ![0,0,1,1,1,0],
    ![0,0,1,1,1,1],
    ![0,1,0,0,0,0],
    ![0,1,0,1,0,0],
    ![0,1,0,1,1,0],
    ![0,1,0,1,1,1],
    ![0,1,1,1,0,0],
    ![0,1,1,1,1,0],
    ![0,1,1,1,1,1],
    ![0,1,1,2,1,0],
    ![0,1,1,2,1,1],
    ![0,1,1,2,2,1],
    ![1,0,0,0,0,0],
    ![1,0,1,0,0,0],
    ![1,0,1,1,0,0],
    ![1,0,1,1,1,0],
    ![1,0,1,1,1,1],
    ![1,1,1,1,0,0],
    ![1,1,1,1,1,0],
    ![1,1,1,1,1,1],
    ![1,1,1,2,1,0],
    ![1,1,1,2,1,1],
    ![1,1,1,2,2,1],
    ![1,1,2,2,1,0],
    ![1,1,2,2,1,1],
    ![1,1,2,2,2,1],
    ![1,1,2,3,2,1],
    ![1,2,2,3,2,1]}

theorem negative_simple_mem : ∀i:Fin 6,-(Pi.single i (1:ℤ):Fin 6→ℤ)∈menu := by decide +kernel

theorem reflection_closed : ∀i:Fin 6,∀x∈menu,reflect CartanMatrix.E₆ i x∈menu := by decide +kernel

theorem menu_card : menu.card=72 := by decide +kernel

theorem positive_menu_card : (menu.filter (fun x=>∀i,0≤x i)).card=36 := by decide +kernel

noncomputable section
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem roots_card_le : Nat.card (Roots CartanMatrix.E₆)≤72 := by
  simpa only [menu_card] using root_card_le CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    menu negative_simple_mem reflection_closed

theorem positive_roots_card_le : Nat.card (PositiveRoot CartanMatrix.E₆)≤36 := by
  simpa only [positive_menu_card] using positive_card_le CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    menu negative_simple_mem reflection_closed

end
end SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu
