import SymmetricSubgroupAsymptotics.CFSGCoTwoPositiveRelatorWords
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoPowerPilot
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts00
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts01
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts02
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts03
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts04
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts05
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts06
import SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoProducts07
import Mathlib.Tactic.FinCases

/-! Actual GL22 pair, exact ten old relators; all data inherited from checked edges. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoRelatorIdentities
open CFSGCoTwoLiteralRepresentation
abbrev M := Matrix (Fin 22) (Fin 22) (ZMod 2)
abbrev Image := Matrix.GeneralLinearGroup (Fin 22) (ZMod 2)
private abbrev A := CFSGCoTwoNativeTwentyTwoBaseCaches.matrixA
private abbrev B := CFSGCoTwoNativeTwentyTwoBaseCaches.matrixB

def unitA : Image where
  val := A
  inv := A
  val_inv := by simpa only [pow_two] using CFSGCoTwoNativeTwentyTwoPowerPilot.wholeA_square
  inv_val := by simpa only [pow_two] using CFSGCoTwoNativeTwentyTwoPowerPilot.wholeA_square

def unitB : Image where
  val := B
  inv := B^4
  val_inv := (pow_succ' B 4).symm.trans CFSGCoTwoNativeTwentyTwoPowerPilot.wholeB_fifth
  inv_val := (pow_succ B 4).symm.trans CFSGCoTwoNativeTwentyTwoPowerPilot.wholeB_fifth

private def u_A : Image := unitA
private def u_B : Image := unitB
private theorem value_A : (u_A : M)=A := rfl
private theorem value_B : (u_B : M)=B := rfl

private def u_A2 : Image := u_A*u_A
private theorem value_A2 : (u_A2 : M)=CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_A2 := by
  change (u_A : M)*(u_A : M)=(A)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_A value_A

private theorem one_A2 : u_A2=1 := by
  apply Units.ext
  exact value_A2.trans (CFSGCoTwoNativeTwentyTwoPowerPilot.cache_A2.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_B2 : Image := u_B*u_B
private theorem value_B2 : (u_B2 : M)=CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2 := by
  change (u_B : M)*(u_B : M)=(B)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_B value_B

private def u_B4 : Image := u_B2*u_B2
private theorem value_B4 : (u_B4 : M)=CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4 := by
  change (u_B2 : M)*(u_B2 : M)=(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)
  exact congrArg₂ (fun x y : M => x*y) value_B2 value_B2

private def u_B5 : Image := u_B4*u_B
private theorem value_B5 : (u_B5 : M)=CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B5 := by
  change (u_B4 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_B4 value_B

private theorem one_B5 : u_B5=1 := by
  apply Units.ext
  exact value_B5.trans (CFSGCoTwoNativeTwentyTwoPowerPilot.cache_B5.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_B3 : Image := u_B2*u_B
private theorem value_B3 : (u_B3 : M)=CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3 := by
  change (u_B2 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_B2 value_B

private def u_R03p01 : Image := u_A*u_B2
private theorem value_R03p01 : (u_R03p01 : M)=CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01 := by
  change (u_A : M)*(u_B2 : M)=(A)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)
  exact congrArg₂ (fun x y : M => x*y) value_A value_B2

private def u_R03e02 : Image := u_R03p01*u_R03p01
private theorem value_R03e02 : (u_R03e02 : M)=CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e02 := by
  change (u_R03p01 : M)*(u_R03p01 : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01)
  exact congrArg₂ (fun x y : M => x*y) value_R03p01 value_R03p01

private def u_R03e04 : Image := u_R03e02*u_R03e02
private theorem value_R03e04 : (u_R03e04 : M)=CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e04 := by
  change (u_R03e02 : M)*(u_R03e02 : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e02)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e02)
  exact congrArg₂ (fun x y : M => x*y) value_R03e02 value_R03e02

private def u_R03e08 : Image := u_R03e04*u_R03e04
private theorem value_R03e08 : (u_R03e08 : M)=CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e08 := by
  change (u_R03e04 : M)*(u_R03e04 : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e04)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e04)
  exact congrArg₂ (fun x y : M => x*y) value_R03e04 value_R03e04

private def u_R03e09 : Image := u_R03e08*u_R03p01
private theorem value_R03e09 : (u_R03e09 : M)=CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e09 := by
  change (u_R03e08 : M)*(u_R03p01 : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03e08)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01)
  exact congrArg₂ (fun x y : M => x*y) value_R03e08 value_R03p01

private theorem one_R03e09 : u_R03e09=1 := by
  apply Units.ext
  exact value_R03e09.trans (CFSGCoTwoNativeTwentyTwoProducts00.cache_R03e09.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_R04p01 : Image := u_A*u_B4
private theorem value_R04p01 : (u_R04p01 : M)=CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p01 := by
  change (u_A : M)*(u_B4 : M)=(A)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)
  exact congrArg₂ (fun x y : M => x*y) value_A value_B4

private def u_R04p02 : Image := u_R04p01*u_A
private theorem value_R04p02 : (u_R04p02 : M)=CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p02 := by
  change (u_R04p01 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p01)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R04p01 value_A

private def u_R04p03 : Image := u_R04p02*u_B
private theorem value_R04p03 : (u_R04p03 : M)=CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04p03 := by
  change (u_R04p02 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p02)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_R04p02 value_B

private def u_R04e02 : Image := u_R04p03*u_R04p03
private theorem value_R04e02 : (u_R04e02 : M)=CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04e02 := by
  change (u_R04p03 : M)*(u_R04p03 : M)=(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04p03)*(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04p03)
  exact congrArg₂ (fun x y : M => x*y) value_R04p03 value_R04p03

private def u_R04e04 : Image := u_R04e02*u_R04e02
private theorem value_R04e04 : (u_R04e04 : M)=CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04e04 := by
  change (u_R04e02 : M)*(u_R04e02 : M)=(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04e02)*(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R04e02)
  exact congrArg₂ (fun x y : M => x*y) value_R04e02 value_R04e02

private theorem one_R04e04 : u_R04e04=1 := by
  apply Units.ext
  exact value_R04e04.trans (CFSGCoTwoNativeTwentyTwoProducts01.cache_R04e04.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_R05p01 : Image := u_A*u_B3
private theorem value_R05p01 : (u_R05p01 : M)=CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p01 := by
  change (u_A : M)*(u_B3 : M)=(A)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)
  exact congrArg₂ (fun x y : M => x*y) value_A value_B3

private def u_R05p02 : Image := u_R05p01*u_A
private theorem value_R05p02 : (u_R05p02 : M)=CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p02 := by
  change (u_R05p01 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p01)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R05p01 value_A

private def u_R05p03 : Image := u_R05p02*u_B2
private theorem value_R05p03 : (u_R05p03 : M)=CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p03 := by
  change (u_R05p02 : M)*(u_B2 : M)=(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p02)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)
  exact congrArg₂ (fun x y : M => x*y) value_R05p02 value_B2

private def u_R05e02 : Image := u_R05p03*u_R05p03
private theorem value_R05e02 : (u_R05e02 : M)=CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05e02 := by
  change (u_R05p03 : M)*(u_R05p03 : M)=(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p03)*(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p03)
  exact congrArg₂ (fun x y : M => x*y) value_R05p03 value_R05p03

private def u_R05e04 : Image := u_R05e02*u_R05e02
private theorem value_R05e04 : (u_R05e04 : M)=CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05e04 := by
  change (u_R05e02 : M)*(u_R05e02 : M)=(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05e02)*(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05e02)
  exact congrArg₂ (fun x y : M => x*y) value_R05e02 value_R05e02

private theorem one_R05e04 : u_R05e04=1 := by
  apply Units.ext
  exact value_R05e04.trans (CFSGCoTwoNativeTwentyTwoProducts01.cache_R05e04.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_R06p03 : Image := u_R04p02*u_B4
private theorem value_R06p03 : (u_R06p03 : M)=CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p03 := by
  change (u_R04p02 : M)*(u_B4 : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p02)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)
  exact congrArg₂ (fun x y : M => x*y) value_R04p02 value_B4

private def u_R06p04 : Image := u_R06p03*u_A
private theorem value_R06p04 : (u_R06p04 : M)=CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p04 := by
  change (u_R06p03 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p03)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R06p03 value_A

private def u_R06p05 : Image := u_R06p04*u_B
private theorem value_R06p05 : (u_R06p05 : M)=CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p05 := by
  change (u_R06p04 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p04)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_R06p04 value_B

private def u_R06p06 : Image := u_R06p05*u_A
private theorem value_R06p06 : (u_R06p06 : M)=CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p06 := by
  change (u_R06p05 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p05)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R06p05 value_A

private def u_R06p07 : Image := u_R06p06*u_B
private theorem value_R06p07 : (u_R06p07 : M)=CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p07 := by
  change (u_R06p06 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p06)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_R06p06 value_B

private def u_R06e02 : Image := u_R06p07*u_R06p07
private theorem value_R06e02 : (u_R06e02 : M)=CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06e02 := by
  change (u_R06p07 : M)*(u_R06p07 : M)=(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p07)*(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p07)
  exact congrArg₂ (fun x y : M => x*y) value_R06p07 value_R06p07

private def u_R06e03 : Image := u_R06e02*u_R06p07
private theorem value_R06e03 : (u_R06e03 : M)=CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06e03 := by
  change (u_R06e02 : M)*(u_R06p07 : M)=(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06e02)*(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R06p07)
  exact congrArg₂ (fun x y : M => x*y) value_R06e02 value_R06p07

private theorem one_R06e03 : u_R06e03=1 := by
  apply Units.ext
  exact value_R06e03.trans (CFSGCoTwoNativeTwentyTwoProducts02.cache_R06e03.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_R07p03 : Image := u_R04p02*u_B3
private theorem value_R07p03 : (u_R07p03 : M)=CFSGCoTwoNativeTwentyTwoProducts02.matrix_R07p03 := by
  change (u_R04p02 : M)*(u_B3 : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R04p02)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)
  exact congrArg₂ (fun x y : M => x*y) value_R04p02 value_B3

private def u_R07p04 : Image := u_R07p03*u_A
private theorem value_R07p04 : (u_R07p04 : M)=CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p04 := by
  change (u_R07p03 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts02.matrix_R07p03)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R07p03 value_A

private def u_R07p05 : Image := u_R07p04*u_B4
private theorem value_R07p05 : (u_R07p05 : M)=CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p05 := by
  change (u_R07p04 : M)*(u_B4 : M)=(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p04)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)
  exact congrArg₂ (fun x y : M => x*y) value_R07p04 value_B4

private def u_R07p06 : Image := u_R07p05*u_A
private theorem value_R07p06 : (u_R07p06 : M)=CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p06 := by
  change (u_R07p05 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p05)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R07p05 value_A

private def u_R07p07 : Image := u_R07p06*u_B
private theorem value_R07p07 : (u_R07p07 : M)=CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p07 := by
  change (u_R07p06 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p06)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_R07p06 value_B

private def u_R07p08 : Image := u_R07p07*u_A
private theorem value_R07p08 : (u_R07p08 : M)=CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p08 := by
  change (u_R07p07 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p07)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R07p07 value_A

private def u_R07p09 : Image := u_R07p08*u_B2
private theorem value_R07p09 : (u_R07p09 : M)=CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p09 := by
  change (u_R07p08 : M)*(u_B2 : M)=(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p08)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)
  exact congrArg₂ (fun x y : M => x*y) value_R07p08 value_B2

private def u_R07p10 : Image := u_R07p09*u_A
private theorem value_R07p10 : (u_R07p10 : M)=CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p10 := by
  change (u_R07p09 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p09)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R07p09 value_A

private def u_R07p11 : Image := u_R07p10*u_B
private theorem value_R07p11 : (u_R07p11 : M)=CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p11 := by
  change (u_R07p10 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p10)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_R07p10 value_B

private def u_R07e02 : Image := u_R07p11*u_R07p11
private theorem value_R07e02 : (u_R07e02 : M)=CFSGCoTwoNativeTwentyTwoProducts04.matrix_R07e02 := by
  change (u_R07p11 : M)*(u_R07p11 : M)=(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p11)*(CFSGCoTwoNativeTwentyTwoProducts03.matrix_R07p11)
  exact congrArg₂ (fun x y : M => x*y) value_R07p11 value_R07p11

private theorem one_R07e02 : u_R07e02=1 := by
  apply Units.ext
  exact value_R07e02.trans (CFSGCoTwoNativeTwentyTwoProducts04.cache_R07e02.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_R08p02 : Image := u_R03p01*u_A
private theorem value_R08p02 : (u_R08p02 : M)=CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p02 := by
  change (u_R03p01 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts00.matrix_R03p01)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R03p01 value_A

private def u_R08p03 : Image := u_R08p02*u_B4
private theorem value_R08p03 : (u_R08p03 : M)=CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p03 := by
  change (u_R08p02 : M)*(u_B4 : M)=(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p02)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)
  exact congrArg₂ (fun x y : M => x*y) value_R08p02 value_B4

private def u_R08p04 : Image := u_R08p03*u_A
private theorem value_R08p04 : (u_R08p04 : M)=CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p04 := by
  change (u_R08p03 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p03)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R08p03 value_A

private def u_R08p05 : Image := u_R08p04*u_B
private theorem value_R08p05 : (u_R08p05 : M)=CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p05 := by
  change (u_R08p04 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p04)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_R08p04 value_B

private def u_R08p06 : Image := u_R08p05*u_A
private theorem value_R08p06 : (u_R08p06 : M)=CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p06 := by
  change (u_R08p05 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p05)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R08p05 value_A

private def u_R08p07 : Image := u_R08p06*u_B3
private theorem value_R08p07 : (u_R08p07 : M)=CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p07 := by
  change (u_R08p06 : M)*(u_B3 : M)=(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p06)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)
  exact congrArg₂ (fun x y : M => x*y) value_R08p06 value_B3

private def u_R08e02 : Image := u_R08p07*u_R08p07
private theorem value_R08e02 : (u_R08e02 : M)=CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08e02 := by
  change (u_R08p07 : M)*(u_R08p07 : M)=(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p07)*(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p07)
  exact congrArg₂ (fun x y : M => x*y) value_R08p07 value_R08p07

private def u_R08e03 : Image := u_R08e02*u_R08p07
private theorem value_R08e03 : (u_R08e03 : M)=CFSGCoTwoNativeTwentyTwoProducts05.matrix_R08e03 := by
  change (u_R08e02 : M)*(u_R08p07 : M)=(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08e02)*(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p07)
  exact congrArg₂ (fun x y : M => x*y) value_R08e02 value_R08p07

private theorem one_R08e03 : u_R08e03=1 := by
  apply Units.ext
  exact value_R08e03.trans (CFSGCoTwoNativeTwentyTwoProducts05.cache_R08e03.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_R09p05 : Image := u_R08p04*u_B2
private theorem value_R09p05 : (u_R09p05 : M)=CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p05 := by
  change (u_R08p04 : M)*(u_B2 : M)=(CFSGCoTwoNativeTwentyTwoProducts04.matrix_R08p04)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)
  exact congrArg₂ (fun x y : M => x*y) value_R08p04 value_B2

private def u_R09p06 : Image := u_R09p05*u_A
private theorem value_R09p06 : (u_R09p06 : M)=CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p06 := by
  change (u_R09p05 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p05)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R09p05 value_A

private def u_R09p07 : Image := u_R09p06*u_B3
private theorem value_R09p07 : (u_R09p07 : M)=CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p07 := by
  change (u_R09p06 : M)*(u_B3 : M)=(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p06)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)
  exact congrArg₂ (fun x y : M => x*y) value_R09p06 value_B3

private def u_R09p08 : Image := u_R09p07*u_A
private theorem value_R09p08 : (u_R09p08 : M)=CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p08 := by
  change (u_R09p07 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p07)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R09p07 value_A

private def u_R09p09 : Image := u_R09p08*u_B
private theorem value_R09p09 : (u_R09p09 : M)=CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p09 := by
  change (u_R09p08 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p08)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_R09p08 value_B

private def u_R09p10 : Image := u_R09p09*u_A
private theorem value_R09p10 : (u_R09p10 : M)=CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p10 := by
  change (u_R09p09 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p09)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R09p09 value_A

private def u_R09p11 : Image := u_R09p10*u_B3
private theorem value_R09p11 : (u_R09p11 : M)=CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p11 := by
  change (u_R09p10 : M)*(u_B3 : M)=(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p10)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)
  exact congrArg₂ (fun x y : M => x*y) value_R09p10 value_B3

private def u_R09e02 : Image := u_R09p11*u_R09p11
private theorem value_R09e02 : (u_R09e02 : M)=CFSGCoTwoNativeTwentyTwoProducts06.matrix_R09e02 := by
  change (u_R09p11 : M)*(u_R09p11 : M)=(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p11)*(CFSGCoTwoNativeTwentyTwoProducts05.matrix_R09p11)
  exact congrArg₂ (fun x y : M => x*y) value_R09p11 value_R09p11

private theorem one_R09e02 : u_R09e02=1 := by
  apply Units.ext
  exact value_R09e02.trans (CFSGCoTwoNativeTwentyTwoProducts06.cache_R09e02.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_R10p01 : Image := u_A*u_B
private theorem value_R10p01 : (u_R10p01 : M)=CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p01 := by
  change (u_A : M)*(u_B : M)=(A)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_A value_B

private def u_R10p02 : Image := u_R10p01*u_A
private theorem value_R10p02 : (u_R10p02 : M)=CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p02 := by
  change (u_R10p01 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p01)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R10p01 value_A

private def u_R10p03 : Image := u_R10p02*u_B2
private theorem value_R10p03 : (u_R10p03 : M)=CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p03 := by
  change (u_R10p02 : M)*(u_B2 : M)=(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p02)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)
  exact congrArg₂ (fun x y : M => x*y) value_R10p02 value_B2

private def u_R10p04 : Image := u_R10p03*u_A
private theorem value_R10p04 : (u_R10p04 : M)=CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p04 := by
  change (u_R10p03 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p03)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R10p03 value_A

private def u_R10p05 : Image := u_R10p04*u_B4
private theorem value_R10p05 : (u_R10p05 : M)=CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p05 := by
  change (u_R10p04 : M)*(u_B4 : M)=(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p04)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B4)
  exact congrArg₂ (fun x y : M => x*y) value_R10p04 value_B4

private def u_R10p06 : Image := u_R10p05*u_A
private theorem value_R10p06 : (u_R10p06 : M)=CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p06 := by
  change (u_R10p05 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p05)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_R10p05 value_A

private def u_R10p07 : Image := u_R10p06*u_B3
private theorem value_R10p07 : (u_R10p07 : M)=CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p07 := by
  change (u_R10p06 : M)*(u_B3 : M)=(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p06)*(CFSGCoTwoNativeTwentyTwoProducts00.matrix_B3)
  exact congrArg₂ (fun x y : M => x*y) value_R10p06 value_B3

private def u_R10e02 : Image := u_R10p07*u_R10p07
private theorem value_R10e02 : (u_R10e02 : M)=CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e02 := by
  change (u_R10p07 : M)*(u_R10p07 : M)=(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p07)*(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p07)
  exact congrArg₂ (fun x y : M => x*y) value_R10p07 value_R10p07

private def u_R10e04 : Image := u_R10e02*u_R10e02
private theorem value_R10e04 : (u_R10e04 : M)=CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e04 := by
  change (u_R10e02 : M)*(u_R10e02 : M)=(CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e02)*(CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e02)
  exact congrArg₂ (fun x y : M => x*y) value_R10e02 value_R10e02

private def u_R10e06 : Image := u_R10e04*u_R10e02
private theorem value_R10e06 : (u_R10e06 : M)=CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e06 := by
  change (u_R10e04 : M)*(u_R10e02 : M)=(CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e04)*(CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e02)
  exact congrArg₂ (fun x y : M => x*y) value_R10e04 value_R10e02

private def u_R10e07 : Image := u_R10e06*u_R10p07
private theorem value_R10e07 : (u_R10e07 : M)=CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e07 := by
  change (u_R10e06 : M)*(u_R10p07 : M)=(CFSGCoTwoNativeTwentyTwoProducts07.matrix_R10e06)*(CFSGCoTwoNativeTwentyTwoProducts06.matrix_R10p07)
  exact congrArg₂ (fun x y : M => x*y) value_R10e06 value_R10p07

private theorem one_R10e07 : u_R10e07=1 := by
  apply Units.ext
  exact value_R10e07.trans (CFSGCoTwoNativeTwentyTwoProducts07.cache_R10e07.trans CFSGCoTwoNativeTwentyTwoBaseCaches.identity_binding)

private def u_Wp03 : Image := u_R05p02*u_B
private theorem value_Wp03 : (u_Wp03 : M)=CFSGCoTwoNativeTwentyTwoProducts07.matrix_Wp03 := by
  change (u_R05p02 : M)*(u_B : M)=(CFSGCoTwoNativeTwentyTwoProducts01.matrix_R05p02)*(B)
  exact congrArg₂ (fun x y : M => x*y) value_R05p02 value_B

private def u_Wp04 : Image := u_Wp03*u_A
private theorem value_Wp04 : (u_Wp04 : M)=CFSGCoTwoNativeTwentyTwoProducts07.matrix_Wp04 := by
  change (u_Wp03 : M)*(u_A : M)=(CFSGCoTwoNativeTwentyTwoProducts07.matrix_Wp03)*(A)
  exact congrArg₂ (fun x y : M => x*y) value_Wp03 value_A

private def u_Wp05 : Image := u_Wp04*u_B2
private theorem value_Wp05 : (u_Wp05 : M)=CFSGCoTwoNativeTwentyTwoProducts07.matrix_Wp05 := by
  change (u_Wp04 : M)*(u_B2 : M)=(CFSGCoTwoNativeTwentyTwoProducts07.matrix_Wp04)*(CFSGCoTwoNativeTwentyTwoPowerPilot.matrix_B2)
  exact congrArg₂ (fun x y : M => x*y) value_Wp04 value_B2

theorem unitA_square : unitA^2=1 := by
  have h : unitA^2=u_A2 := by
    simpa only [pow_two] using (show unitA*unitA=u_A2 from rfl)
  exact h.trans one_A2

theorem unitB_fifth : unitB^5=1 := by
  apply Units.ext
  change B^5=1
  exact CFSGCoTwoNativeTwentyTwoPowerPilot.wholeB_fifth

private theorem b1_word : unitB^1=u_B := by
  simpa only [pow_one] using (show unitB=u_B from rfl)

private theorem b2_word : unitB^2=u_B2 := by
  calc
    unitB^2=unitB^1*unitB^1 := pow_add unitB 1 1
    _=u_B*u_B := congrArg₂ (fun x y : Image => x*y) b1_word b1_word
    _=u_B2 := rfl

private theorem b3_word : unitB^3=u_B3 := by
  calc
    unitB^3=unitB^2*unitB^1 := pow_add unitB 2 1
    _=u_B2*u_B := congrArg₂ (fun x y : Image => x*y) b2_word b1_word
    _=u_B3 := rfl

private theorem b4_word : unitB^4=u_B4 := by
  calc
    unitB^4=unitB^2*unitB^2 := pow_add unitB 2 2
    _=u_B2*u_B2 := congrArg₂ (fun x y : Image => x*y) b2_word b2_word
    _=u_B4 := rfl

private theorem b5_word : unitB^5=u_B5 := by
  calc
    unitB^5=unitB^4*unitB^1 := pow_add unitB 4 1
    _=u_B4*u_B := congrArg₂ (fun x y : Image => x*y) b4_word b1_word
    _=u_B5 := rfl

private theorem r3_word : CFSGCoTwoPositiveRelatorWords.r3 unitA unitB=u_R03p01 := by
  simpa only [CFSGCoTwoPositiveRelatorWords.r3,b2_word,b3_word,b4_word] using
    (show unitA*u_B2=u_R03p01 from rfl)

private theorem r3e1_word : (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^1=u_R03p01 := by
  simpa only [pow_one] using r3_word

private theorem r3e2_word : (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^2=u_R03e02 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^2=(CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^1*(CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^1 := pow_add _ 1 1
    _=u_R03p01*u_R03p01 := congrArg₂ (fun x y : Image => x*y) r3e1_word r3e1_word
    _=u_R03e02 := rfl

private theorem r3e4_word : (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^4=u_R03e04 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^4=(CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^2*(CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^2 := pow_add _ 2 2
    _=u_R03e02*u_R03e02 := congrArg₂ (fun x y : Image => x*y) r3e2_word r3e2_word
    _=u_R03e04 := rfl

private theorem r3e8_word : (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^8=u_R03e08 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^8=(CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^4*(CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^4 := pow_add _ 4 4
    _=u_R03e04*u_R03e04 := congrArg₂ (fun x y : Image => x*y) r3e4_word r3e4_word
    _=u_R03e08 := rfl

private theorem r3e9_word : (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^9=u_R03e09 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^9=(CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^8*(CFSGCoTwoPositiveRelatorWords.r3 unitA unitB)^1 := pow_add _ 8 1
    _=u_R03e08*u_R03p01 := congrArg₂ (fun x y : Image => x*y) r3e8_word r3e1_word
    _=u_R03e09 := rfl

private theorem r4_word : CFSGCoTwoPositiveRelatorWords.r4 unitA unitB=u_R04p03 := by
  simpa only [CFSGCoTwoPositiveRelatorWords.r4,b2_word,b3_word,b4_word] using
    (show unitA*u_B4*unitA*unitB=u_R04p03 from rfl)

private theorem r4e1_word : (CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^1=u_R04p03 := by
  simpa only [pow_one] using r4_word

private theorem r4e2_word : (CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^2=u_R04e02 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^2=(CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^1*(CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^1 := pow_add _ 1 1
    _=u_R04p03*u_R04p03 := congrArg₂ (fun x y : Image => x*y) r4e1_word r4e1_word
    _=u_R04e02 := rfl

private theorem r4e4_word : (CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^4=u_R04e04 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^4=(CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^2*(CFSGCoTwoPositiveRelatorWords.r4 unitA unitB)^2 := pow_add _ 2 2
    _=u_R04e02*u_R04e02 := congrArg₂ (fun x y : Image => x*y) r4e2_word r4e2_word
    _=u_R04e04 := rfl

private theorem r5_word : CFSGCoTwoPositiveRelatorWords.r5 unitA unitB=u_R05p03 := by
  simpa only [CFSGCoTwoPositiveRelatorWords.r5,b2_word,b3_word,b4_word] using
    (show unitA*u_B3*unitA*u_B2=u_R05p03 from rfl)

private theorem r5e1_word : (CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^1=u_R05p03 := by
  simpa only [pow_one] using r5_word

private theorem r5e2_word : (CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^2=u_R05e02 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^2=(CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^1*(CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^1 := pow_add _ 1 1
    _=u_R05p03*u_R05p03 := congrArg₂ (fun x y : Image => x*y) r5e1_word r5e1_word
    _=u_R05e02 := rfl

private theorem r5e4_word : (CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^4=u_R05e04 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^4=(CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^2*(CFSGCoTwoPositiveRelatorWords.r5 unitA unitB)^2 := pow_add _ 2 2
    _=u_R05e02*u_R05e02 := congrArg₂ (fun x y : Image => x*y) r5e2_word r5e2_word
    _=u_R05e04 := rfl

private theorem r6_word : CFSGCoTwoPositiveRelatorWords.r6 unitA unitB=u_R06p07 := by
  simpa only [CFSGCoTwoPositiveRelatorWords.r6,b2_word,b3_word,b4_word] using
    (show unitA*u_B4*unitA*u_B4*unitA*unitB*unitA*unitB=u_R06p07 from rfl)

private theorem r6e1_word : (CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^1=u_R06p07 := by
  simpa only [pow_one] using r6_word

private theorem r6e2_word : (CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^2=u_R06e02 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^2=(CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^1*(CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^1 := pow_add _ 1 1
    _=u_R06p07*u_R06p07 := congrArg₂ (fun x y : Image => x*y) r6e1_word r6e1_word
    _=u_R06e02 := rfl

private theorem r6e3_word : (CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^3=u_R06e03 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^3=(CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^2*(CFSGCoTwoPositiveRelatorWords.r6 unitA unitB)^1 := pow_add _ 2 1
    _=u_R06e02*u_R06p07 := congrArg₂ (fun x y : Image => x*y) r6e2_word r6e1_word
    _=u_R06e03 := rfl

private theorem r7_word : CFSGCoTwoPositiveRelatorWords.r7 unitA unitB=u_R07p11 := by
  simpa only [CFSGCoTwoPositiveRelatorWords.r7,b2_word,b3_word,b4_word] using
    (show unitA*u_B4*unitA*u_B3*unitA*u_B4*unitA*unitB*unitA*u_B2*unitA*unitB=u_R07p11 from rfl)

private theorem r7e1_word : (CFSGCoTwoPositiveRelatorWords.r7 unitA unitB)^1=u_R07p11 := by
  simpa only [pow_one] using r7_word

private theorem r7e2_word : (CFSGCoTwoPositiveRelatorWords.r7 unitA unitB)^2=u_R07e02 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r7 unitA unitB)^2=(CFSGCoTwoPositiveRelatorWords.r7 unitA unitB)^1*(CFSGCoTwoPositiveRelatorWords.r7 unitA unitB)^1 := pow_add _ 1 1
    _=u_R07p11*u_R07p11 := congrArg₂ (fun x y : Image => x*y) r7e1_word r7e1_word
    _=u_R07e02 := rfl

private theorem r8_word : CFSGCoTwoPositiveRelatorWords.r8 unitA unitB=u_R08p07 := by
  simpa only [CFSGCoTwoPositiveRelatorWords.r8,b2_word,b3_word,b4_word] using
    (show unitA*u_B2*unitA*u_B4*unitA*unitB*unitA*u_B3=u_R08p07 from rfl)

private theorem r8e1_word : (CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^1=u_R08p07 := by
  simpa only [pow_one] using r8_word

private theorem r8e2_word : (CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^2=u_R08e02 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^2=(CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^1*(CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^1 := pow_add _ 1 1
    _=u_R08p07*u_R08p07 := congrArg₂ (fun x y : Image => x*y) r8e1_word r8e1_word
    _=u_R08e02 := rfl

private theorem r8e3_word : (CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^3=u_R08e03 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^3=(CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^2*(CFSGCoTwoPositiveRelatorWords.r8 unitA unitB)^1 := pow_add _ 2 1
    _=u_R08e02*u_R08p07 := congrArg₂ (fun x y : Image => x*y) r8e2_word r8e1_word
    _=u_R08e03 := rfl

private theorem r9_word : CFSGCoTwoPositiveRelatorWords.r9 unitA unitB=u_R09p11 := by
  simpa only [CFSGCoTwoPositiveRelatorWords.r9,b2_word,b3_word,b4_word] using
    (show unitA*u_B2*unitA*u_B4*unitA*u_B2*unitA*u_B3*unitA*unitB*unitA*u_B3=u_R09p11 from rfl)

private theorem r9e1_word : (CFSGCoTwoPositiveRelatorWords.r9 unitA unitB)^1=u_R09p11 := by
  simpa only [pow_one] using r9_word

private theorem r9e2_word : (CFSGCoTwoPositiveRelatorWords.r9 unitA unitB)^2=u_R09e02 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r9 unitA unitB)^2=(CFSGCoTwoPositiveRelatorWords.r9 unitA unitB)^1*(CFSGCoTwoPositiveRelatorWords.r9 unitA unitB)^1 := pow_add _ 1 1
    _=u_R09p11*u_R09p11 := congrArg₂ (fun x y : Image => x*y) r9e1_word r9e1_word
    _=u_R09e02 := rfl

private theorem r10_word : CFSGCoTwoPositiveRelatorWords.r10 unitA unitB=u_R10p07 := by
  simpa only [CFSGCoTwoPositiveRelatorWords.r10,b2_word,b3_word,b4_word] using
    (show unitA*unitB*unitA*u_B2*unitA*u_B4*unitA*u_B3=u_R10p07 from rfl)

private theorem r10e1_word : (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^1=u_R10p07 := by
  simpa only [pow_one] using r10_word

private theorem r10e2_word : (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^2=u_R10e02 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^2=(CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^1*(CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^1 := pow_add _ 1 1
    _=u_R10p07*u_R10p07 := congrArg₂ (fun x y : Image => x*y) r10e1_word r10e1_word
    _=u_R10e02 := rfl

private theorem r10e4_word : (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^4=u_R10e04 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^4=(CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^2*(CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^2 := pow_add _ 2 2
    _=u_R10e02*u_R10e02 := congrArg₂ (fun x y : Image => x*y) r10e2_word r10e2_word
    _=u_R10e04 := rfl

private theorem r10e6_word : (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^6=u_R10e06 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^6=(CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^4*(CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^2 := pow_add _ 4 2
    _=u_R10e04*u_R10e02 := congrArg₂ (fun x y : Image => x*y) r10e4_word r10e2_word
    _=u_R10e06 := rfl

private theorem r10e7_word : (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^7=u_R10e07 := by
  calc
    (CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^7=(CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^6*(CFSGCoTwoPositiveRelatorWords.r10 unitA unitB)^1 := pow_add _ 6 1
    _=u_R10e06*u_R10p07 := congrArg₂ (fun x y : Image => x*y) r10e6_word r10e1_word
    _=u_R10e07 := rfl

theorem relatorPacket : RelatorPacket unitA unitB :=
  CFSGCoTwoPositiveRelatorWords.packet_of_positive_powers unitA unitB
    unitA_square unitB_fifth
    (r3e9_word.trans one_R03e09)
    (r4e4_word.trans one_R04e04)
    (r5e4_word.trans one_R05e04)
    (r6e3_word.trans one_R06e03)
    (r7e2_word.trans one_R07e02)
    (r8e3_word.trans one_R08e03)
    (r9e2_word.trans one_R09e02)
    (r10e7_word.trans one_R10e07)

private theorem w_word : positiveWord unitA unitB=u_Wp05 := by
  simpa only [positiveWord,b2_word,b3_word] using
    (show unitA*u_B3*unitA*unitB*unitA*u_B2=u_Wp05 from rfl)

theorem selectedWord_value : ((positiveWord unitA unitB : Image) : M)=CFSGCoTwoNativeTwentyTwoCaches13.Wp05_data.matrix 2 :=
  (congrArg (fun u : Image => (u : M)) w_word).trans
    (value_Wp05.trans CFSGCoTwoNativeTwentyTwoProducts07.cache_Wp05)

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoRelatorIdentities
