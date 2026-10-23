import SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameFibresPilot

/-! A bounded six-root certificate for the last orthogonal-frame fibre.
Only positive first roots with zeroth coordinate 0 are selected here.
This is a root-menu calculation, not a Weyl-word census. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameTripleZero
open CFSGFFourE6FixedRootFramePilot CFSGIntegerMatrixPairing

def firstRoots : Finset (Fin 6→ℤ) := menu.filter
  (fun x=>(∀i,0≤x i)∧x 0=0)

theorem firstRoots_card : firstRoots.card=6 := by decide +kernel

theorem triple_orthogonal_card : ∀x∈firstRoots,∀y∈menu,∀z∈menu,
    integerPairing CartanMatrix.E₆ x y=0→
    integerPairing CartanMatrix.E₆ x z=0→integerPairing CartanMatrix.E₆ y z=0→
      (menu.filter (fun w=>integerPairing CartanMatrix.E₆ x w=0∧
        integerPairing CartanMatrix.E₆ y w=0∧integerPairing CartanMatrix.E₆ z w=0)).card=2 :=
  by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameTripleZero
