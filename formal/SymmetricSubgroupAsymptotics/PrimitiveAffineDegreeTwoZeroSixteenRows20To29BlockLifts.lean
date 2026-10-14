import SymmetricSubgroupAsymptotics.BinaryFourSymmetricBlockLiteralChart

/-! Exact generator bindings for the ten S4 block families on sixteen
original points. The displayed translations include every nonsplit lift.
These bindings do not assert a normal-generator or capacity bound. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenRows20To29BlockLifts

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourSymmetricBlockActions

def row20Lifts : Fin 5 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 0,
    literalLift ![1, 0, 0, 0, 0, 0, 1, 0] 1,
    literalLift ![0, 0, 0, 0, 0, 1, 0, 0] 2,
    literalLift ![0, 1, 0, 0, 1, 1, 0, 0] 3,
    literalLift ![1, 1, 1, 0, 1, 0, 0, 0] 4]

theorem row20_binding (i : Fin 5) :
    literalPermutation (row20Lifts i) = DegreeTwoZeroSixteenInterfaces.row20Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row21Lifts : Fin 5 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 0,
    literalLift ![0, 0, 1, 0, 1, 1, 1, 0] 1,
    literalLift ![0, 0, 0, 0, 0, 1, 0, 0] 2,
    literalLift ![0, 1, 0, 0, 1, 1, 0, 0] 3,
    literalLift ![1, 1, 0, 1, 0, 1, 0, 0] 4]

theorem row21_binding (i : Fin 5) :
    literalPermutation (row21Lifts i) = DegreeTwoZeroSixteenInterfaces.row21Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row22Lifts : Fin 4 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 0,
    literalLift ![0, 0, 1, 0, 1, 1, 1, 0] 1,
    literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 2,
    literalLift ![0, 0, 1, 0, 1, 0, 0, 0] 3]

theorem row22_binding (i : Fin 4) :
    literalPermutation (row22Lifts i) = DegreeTwoZeroSixteenInterfaces.row22Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row23Lifts : Fin 5 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 0,
    literalLift ![0, 1, 1, 1, 0, 0, 1, 0] 1,
    literalLift ![0, 0, 0, 0, 0, 1, 0, 0] 2,
    literalLift ![0, 1, 0, 0, 1, 1, 0, 0] 3,
    literalLift ![1, 1, 0, 0, 0, 1, 0, 0] 4]

theorem row23_binding (i : Fin 5) :
    literalPermutation (row23Lifts i) = DegreeTwoZeroSixteenInterfaces.row23Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row24Lifts : Fin 4 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 0,
    literalLift ![0, 1, 1, 1, 0, 0, 1, 0] 1,
    literalLift ![0, 0, 0, 0, 1, 1, 1, 1] 2,
    literalLift ![0, 0, 1, 1, 0, 0, 0, 1] 3]

theorem row24_binding (i : Fin 4) :
    literalPermutation (row24Lifts i) = DegreeTwoZeroSixteenInterfaces.row24Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row25Lifts : Fin 4 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 1, 0, 1, 1] 0,
    literalLift ![0, 1, 1, 0, 1, 1, 1, 1] 1,
    literalLift ![0, 1, 1, 0, 0, 1, 0, 0] 2,
    literalLift ![0, 0, 1, 0, 1, 1, 0, 0] 3]

theorem row25_binding (i : Fin 4) :
    literalPermutation (row25Lifts i) = DegreeTwoZeroSixteenInterfaces.row25Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row26Lifts : Fin 4 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 1, 0, 1, 1] 0,
    literalLift ![0, 1, 1, 0, 1, 1, 1, 1] 1,
    literalLift ![0, 1, 1, 0, 1, 1, 1, 1] 2,
    literalLift ![0, 1, 0, 1, 0, 0, 0, 1] 3]

theorem row26_binding (i : Fin 4) :
    literalPermutation (row26Lifts i) = DegreeTwoZeroSixteenInterfaces.row26Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row27Lifts : Fin 4 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 0,
    literalLift ![0, 0, 0, 1, 0, 0, 1, 0] 1,
    literalLift ![0, 0, 0, 0, 0, 1, 0, 0] 2,
    literalLift ![0, 1, 0, 0, 1, 1, 0, 0] 3]

theorem row27_binding (i : Fin 4) :
    literalPermutation (row27Lifts i) = DegreeTwoZeroSixteenInterfaces.row27Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row28Lifts : Fin 4 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 0,
    literalLift ![0, 0, 0, 1, 0, 0, 1, 0] 1,
    literalLift ![0, 0, 0, 0, 1, 1, 1, 1] 2,
    literalLift ![0, 0, 1, 1, 0, 0, 0, 1] 3]

theorem row28_binding (i : Fin 4) :
    literalPermutation (row28Lifts i) = DegreeTwoZeroSixteenInterfaces.row28Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def row29Lifts : Fin 4 → SymmetricAmbient :=
  ![literalLift ![0, 0, 0, 1, 1, 0, 0, 1] 0,
    literalLift ![0, 0, 0, 0, 0, 0, 0, 0] 1,
    literalLift ![0, 0, 0, 0, 0, 1, 0, 0] 2,
    literalLift ![0, 1, 0, 0, 1, 1, 0, 0] 3]

theorem row29_binding (i : Fin 4) :
    literalPermutation (row29Lifts i) = DegreeTwoZeroSixteenInterfaces.row29Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

end PrimitiveAffineDegreeTwoZeroSixteenRows20To29BlockLifts
end SymmetricSubgroupAsymptotics

end
