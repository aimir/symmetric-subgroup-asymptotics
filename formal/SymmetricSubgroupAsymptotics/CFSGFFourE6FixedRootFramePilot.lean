import SymmetricSubgroupAsymptotics.CFSGE6FixedPositiveRootMenu

/-! Small literal geometry pilot for the F4 relative Weyl frame count.
The menu is the diagram-fixed part of the already complete E6 menu;
no Weyl-word enumeration occurs. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FixedRootFramePilot
open CFSGIntegerMatrixPairing

def menu : Finset (Fin 6→ℤ) := CFSGE6FiniteRootMenu.menu.filter
  (fun x=>∀i,x (CFSG.Models.e6Twist i)=x i)

def frame : Fin 4→Fin 6→ℤ := ![
  ![0,0,0,1,0,0], ![0,0,1,1,1,0],
  ![1,0,1,1,1,1], ![1,2,2,3,2,1]]

def regular : Fin 6→ℤ := ![16,22,30,42,30,16]

theorem menu_card : menu.card=24 := by decide +kernel

theorem frame_mem : ∀i:Fin 4,frame i∈menu := by decide +kernel

theorem frame_norm : ∀i:Fin 4,integerPairing CartanMatrix.E₆ (frame i) (frame i)=2 := by decide +kernel

theorem frame_orthogonal : ∀i j:Fin 4,i≠j→
    integerPairing CartanMatrix.E₆ (frame i) (frame j)=0 := by decide +kernel

theorem regular_combination :
    regular=frame 0+3 • frame 1+5 • frame 2+11 • frame 3 := by decide +kernel

theorem regular_simple_pairing : ∀j:Fin 6,
    integerPairing CartanMatrix.E₆ regular (Pi.single j (1:ℤ))=2 := by decide +kernel

theorem orthogonal_card : ∀x∈menu,
    (menu.filter (fun y=>integerPairing CartanMatrix.E₆ x y=0)).card=6 := by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourE6FixedRootFramePilot
