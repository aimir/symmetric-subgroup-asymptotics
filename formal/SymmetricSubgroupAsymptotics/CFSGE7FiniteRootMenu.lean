import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFiniteRootMenu
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! A literal reflection-stable menu for the pinned E7 integer lattice.
Negative-simple membership, reflection closure, and both menu sizes are
kernel-checked. Coverage is deduced from the root-word orbit theorem. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGE7FiniteRootMenu
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateFiniteRootMenu CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGExceptionalCartanPositiveDefinite

def menu : Finset (Fin 7→ℤ) := {
    ![-2,-2,-3,-4,-3,-2,-1],
    ![-1,-2,-3,-4,-3,-2,-1],
    ![-1,-2,-2,-4,-3,-2,-1],
    ![-1,-2,-2,-3,-3,-2,-1],
    ![-1,-2,-2,-3,-2,-2,-1],
    ![-1,-2,-2,-3,-2,-1,-1],
    ![-1,-2,-2,-3,-2,-1,0],
    ![-1,-1,-2,-3,-3,-2,-1],
    ![-1,-1,-2,-3,-2,-2,-1],
    ![-1,-1,-2,-3,-2,-1,-1],
    ![-1,-1,-2,-3,-2,-1,0],
    ![-1,-1,-2,-2,-2,-2,-1],
    ![-1,-1,-2,-2,-2,-1,-1],
    ![-1,-1,-2,-2,-2,-1,0],
    ![-1,-1,-2,-2,-1,-1,-1],
    ![-1,-1,-2,-2,-1,-1,0],
    ![-1,-1,-2,-2,-1,0,0],
    ![-1,-1,-1,-2,-2,-2,-1],
    ![-1,-1,-1,-2,-2,-1,-1],
    ![-1,-1,-1,-2,-2,-1,0],
    ![-1,-1,-1,-2,-1,-1,-1],
    ![-1,-1,-1,-2,-1,-1,0],
    ![-1,-1,-1,-2,-1,0,0],
    ![-1,-1,-1,-1,-1,-1,-1],
    ![-1,-1,-1,-1,-1,-1,0],
    ![-1,-1,-1,-1,-1,0,0],
    ![-1,-1,-1,-1,0,0,0],
    ![-1,0,-1,-1,-1,-1,-1],
    ![-1,0,-1,-1,-1,-1,0],
    ![-1,0,-1,-1,-1,0,0],
    ![-1,0,-1,-1,0,0,0],
    ![-1,0,-1,0,0,0,0],
    ![-1,0,0,0,0,0,0],
    ![0,-1,-1,-2,-2,-2,-1],
    ![0,-1,-1,-2,-2,-1,-1],
    ![0,-1,-1,-2,-2,-1,0],
    ![0,-1,-1,-2,-1,-1,-1],
    ![0,-1,-1,-2,-1,-1,0],
    ![0,-1,-1,-2,-1,0,0],
    ![0,-1,-1,-1,-1,-1,-1],
    ![0,-1,-1,-1,-1,-1,0],
    ![0,-1,-1,-1,-1,0,0],
    ![0,-1,-1,-1,0,0,0],
    ![0,-1,0,-1,-1,-1,-1],
    ![0,-1,0,-1,-1,-1,0],
    ![0,-1,0,-1,-1,0,0],
    ![0,-1,0,-1,0,0,0],
    ![0,-1,0,0,0,0,0],
    ![0,0,-1,-1,-1,-1,-1],
    ![0,0,-1,-1,-1,-1,0],
    ![0,0,-1,-1,-1,0,0],
    ![0,0,-1,-1,0,0,0],
    ![0,0,-1,0,0,0,0],
    ![0,0,0,-1,-1,-1,-1],
    ![0,0,0,-1,-1,-1,0],
    ![0,0,0,-1,-1,0,0],
    ![0,0,0,-1,0,0,0],
    ![0,0,0,0,-1,-1,-1],
    ![0,0,0,0,-1,-1,0],
    ![0,0,0,0,-1,0,0],
    ![0,0,0,0,0,-1,-1],
    ![0,0,0,0,0,-1,0],
    ![0,0,0,0,0,0,-1],
    ![0,0,0,0,0,0,1],
    ![0,0,0,0,0,1,0],
    ![0,0,0,0,0,1,1],
    ![0,0,0,0,1,0,0],
    ![0,0,0,0,1,1,0],
    ![0,0,0,0,1,1,1],
    ![0,0,0,1,0,0,0],
    ![0,0,0,1,1,0,0],
    ![0,0,0,1,1,1,0],
    ![0,0,0,1,1,1,1],
    ![0,0,1,0,0,0,0],
    ![0,0,1,1,0,0,0],
    ![0,0,1,1,1,0,0],
    ![0,0,1,1,1,1,0],
    ![0,0,1,1,1,1,1],
    ![0,1,0,0,0,0,0],
    ![0,1,0,1,0,0,0],
    ![0,1,0,1,1,0,0],
    ![0,1,0,1,1,1,0],
    ![0,1,0,1,1,1,1],
    ![0,1,1,1,0,0,0],
    ![0,1,1,1,1,0,0],
    ![0,1,1,1,1,1,0],
    ![0,1,1,1,1,1,1],
    ![0,1,1,2,1,0,0],
    ![0,1,1,2,1,1,0],
    ![0,1,1,2,1,1,1],
    ![0,1,1,2,2,1,0],
    ![0,1,1,2,2,1,1],
    ![0,1,1,2,2,2,1],
    ![1,0,0,0,0,0,0],
    ![1,0,1,0,0,0,0],
    ![1,0,1,1,0,0,0],
    ![1,0,1,1,1,0,0],
    ![1,0,1,1,1,1,0],
    ![1,0,1,1,1,1,1],
    ![1,1,1,1,0,0,0],
    ![1,1,1,1,1,0,0],
    ![1,1,1,1,1,1,0],
    ![1,1,1,1,1,1,1],
    ![1,1,1,2,1,0,0],
    ![1,1,1,2,1,1,0],
    ![1,1,1,2,1,1,1],
    ![1,1,1,2,2,1,0],
    ![1,1,1,2,2,1,1],
    ![1,1,1,2,2,2,1],
    ![1,1,2,2,1,0,0],
    ![1,1,2,2,1,1,0],
    ![1,1,2,2,1,1,1],
    ![1,1,2,2,2,1,0],
    ![1,1,2,2,2,1,1],
    ![1,1,2,2,2,2,1],
    ![1,1,2,3,2,1,0],
    ![1,1,2,3,2,1,1],
    ![1,1,2,3,2,2,1],
    ![1,1,2,3,3,2,1],
    ![1,2,2,3,2,1,0],
    ![1,2,2,3,2,1,1],
    ![1,2,2,3,2,2,1],
    ![1,2,2,3,3,2,1],
    ![1,2,2,4,3,2,1],
    ![1,2,3,4,3,2,1],
    ![2,2,3,4,3,2,1]}

theorem negative_simple_mem : ∀i:Fin 7,-(Pi.single i (1:ℤ):Fin 7→ℤ)∈menu := by decide +kernel

theorem reflection_closed : ∀i:Fin 7,∀x∈menu,reflect CartanMatrix.E₇ i x∈menu := by decide +kernel

theorem menu_card : menu.card=126 := by decide +kernel

theorem positive_menu_card : (menu.filter (fun x=>∀i,0≤x i)).card=63 := by decide +kernel

attribute [irreducible] menu

noncomputable section
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _

theorem roots_card_le : Nat.card (Roots CartanMatrix.E₇)≤126 := by
  have h : Nat.card (Roots CartanMatrix.E₇)≤menu.card := root_card_le CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos
    menu negative_simple_mem reflection_closed
  exact h.trans_eq menu_card

theorem positive_roots_card_le : Nat.card (PositiveRoot CartanMatrix.E₇)≤63 := by
  have h : Nat.card (PositiveRoot CartanMatrix.E₇)≤(menu.filter (fun x=>∀i,0≤x i)).card := positive_card_le CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos
    menu negative_simple_mem reflection_closed
  exact h.trans_eq positive_menu_card

end
end SymmetricSubgroupAsymptotics.CFSGE7FiniteRootMenu
