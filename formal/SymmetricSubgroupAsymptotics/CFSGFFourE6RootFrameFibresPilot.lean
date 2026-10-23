import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedRootFramePilot

/-! Bounded local orthogonality fibres in the fixed 24-root menu.
The triple pilot fixes the first root; it is not a Weyl group census. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameFibresPilot
open CFSGFFourE6FixedRootFramePilot CFSGIntegerMatrixPairing

theorem pair_orthogonal_card : ∀x∈menu,∀y∈menu,
    integerPairing CartanMatrix.E₆ x y=0→
      (menu.filter (fun z=>integerPairing CartanMatrix.E₆ x z=0∧
        integerPairing CartanMatrix.E₆ y z=0)).card=4 := by decide +kernel

theorem triple_orthogonal_card_pilot : ∀y∈menu,∀z∈menu,
    integerPairing CartanMatrix.E₆ (frame 0) y=0→
    integerPairing CartanMatrix.E₆ (frame 0) z=0→integerPairing CartanMatrix.E₆ y z=0→
      (menu.filter (fun w=>integerPairing CartanMatrix.E₆ (frame 0) w=0∧
        integerPairing CartanMatrix.E₆ y w=0∧integerPairing CartanMatrix.E₆ z w=0)).card=2 := by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourE6RootFrameFibresPilot
