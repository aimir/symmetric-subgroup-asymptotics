import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassBase
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 169: pair-top data

This is a resource-bounded split of the selected action-169 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

private def topRow0 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,2,5,3,1,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,4,1,3,0,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow1 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,5,2,4,1,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,4,2,0,3,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow2 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,1,4,3,2,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,1,4,3,2,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow3 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,1,5,2,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,2,4,0,1,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow4 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,4,5,1,3,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,3,0,4,1,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow5 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,5,4,2,3,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,0,3,4,2,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow6 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,3,2,1,4,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,3,2,1,4,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow7 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,2,3,5,4,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,0,1,2,4,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow8 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,3,1,2,5,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,2,3,1,0,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow9 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,1,3,4,5,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,1,0,2,3,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow10 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,4,3,2,1,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,4,3,2,1,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow11 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,4,5,1,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,4,0,1,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow12 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,5,3,1,2,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,3,4,2,0,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow13 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,3,5,4,2,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,0,4,1,3,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow14 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,2,1,4,3,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,2,1,4,3,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow15 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,1,2,5,3,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,1,2,4,0,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow16 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,1,5,2,4,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,1,3,0,4,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow17 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,5,1,3,4,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,2,0,3,4,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow18 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,2,4,1,5,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,3,1,0,2,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow19 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,4,2,3,5,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,0,2,3,1,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow20 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,3,4,2,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,3,1,2,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow21 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,4,3,5,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,0,2,1,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow22 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,5,4,0,2,1] : Array (Fin 6))[x.val]!
  invFun x := (#[3,5,4,0,2,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow23 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,4,5,3,2,1] : Array (Fin 6))[x.val]!
  invFun x := (#[0,5,4,3,1,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow24 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,0,5,2,3,1] : Array (Fin 6))[x.val]!
  invFun x := (#[1,5,3,4,0,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow25 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,5,0,4,3,1] : Array (Fin 6))[x.val]!
  invFun x := (#[2,5,0,4,3,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow26 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,2,0,3,4,1] : Array (Fin 6))[x.val]!
  invFun x := (#[2,5,1,3,4,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow27 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,0,2,5,4,1] : Array (Fin 6))[x.val]!
  invFun x := (#[1,5,2,0,4,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow28 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,2,3,0,5,1] : Array (Fin 6))[x.val]!
  invFun x := (#[3,5,1,2,0,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow29 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,3,2,4,5,1] : Array (Fin 6))[x.val]!
  invFun x := (#[0,5,2,1,3,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow30 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,5,2,3,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,2,3,0,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow31 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,2,5,4,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,1,0,3,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow32 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,0,3,4,2,1] : Array (Fin 6))[x.val]!
  invFun x := (#[1,5,4,2,3,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow33 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,3,0,5,2,1] : Array (Fin 6))[x.val]!
  invFun x := (#[2,5,4,1,0,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow34 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,4,2,0,3,1] : Array (Fin 6))[x.val]!
  invFun x := (#[3,5,2,4,1,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow35 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,2,4,5,3,1] : Array (Fin 6))[x.val]!
  invFun x := (#[0,5,1,4,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow36 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,5,0,4,1] : Array (Fin 6))[x.val]!
  invFun x := (#[3,5,0,1,4,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow37 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,5,3,2,4,1] : Array (Fin 6))[x.val]!
  invFun x := (#[0,5,3,2,4,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow38 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,0,2,5,1] : Array (Fin 6))[x.val]!
  invFun x := (#[2,5,3,0,1,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow39 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,0,4,3,5,1] : Array (Fin 6))[x.val]!
  invFun x := (#[1,5,0,3,2,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow40 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,4,1,3,0,2] : Array (Fin 6))[x.val]!
  invFun x := (#[4,2,5,3,1,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow41 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,1,4,5,0,2] : Array (Fin 6))[x.val]!
  invFun x := (#[4,1,5,0,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow42 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,3,0,4,1,2] : Array (Fin 6))[x.val]!
  invFun x := (#[2,4,5,1,3,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow43 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,0,3,5,1,2] : Array (Fin 6))[x.val]!
  invFun x := (#[1,4,5,2,0,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow44 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,5,1,0,3,2] : Array (Fin 6))[x.val]!
  invFun x := (#[3,2,5,4,0,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow45 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,1,5,4,3,2] : Array (Fin 6))[x.val]!
  invFun x := (#[0,1,5,4,3,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow46 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,5,0,1,4,2] : Array (Fin 6))[x.val]!
  invFun x := (#[2,3,5,0,4,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow47 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,0,5,3,4,2] : Array (Fin 6))[x.val]!
  invFun x := (#[1,0,5,3,4,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow48 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,3,4,0,5,2] : Array (Fin 6))[x.val]!
  invFun x := (#[3,0,5,1,2,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow49 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,4,3,1,5,2] : Array (Fin 6))[x.val]!
  invFun x := (#[0,3,5,2,1,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow50 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,3,5,1,0,2] : Array (Fin 6))[x.val]!
  invFun x := (#[4,3,5,1,0,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow51 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,5,3,4,0,2] : Array (Fin 6))[x.val]!
  invFun x := (#[4,0,5,2,3,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow52 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,5,0,1,2] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,5,0,1,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow53 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,5,4,3,1,2] : Array (Fin 6))[x.val]!
  invFun x := (#[0,4,5,3,2,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow54 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,0,4,1,3,2] : Array (Fin 6))[x.val]!
  invFun x := (#[1,3,5,4,2,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow55 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,4,0,5,3,2] : Array (Fin 6))[x.val]!
  invFun x := (#[2,0,5,4,1,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow56 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,1,3,0,4,2] : Array (Fin 6))[x.val]!
  invFun x := (#[3,1,5,2,4,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow57 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,3,1,5,4,2] : Array (Fin 6))[x.val]!
  invFun x := (#[0,2,5,1,4,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow58 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,1,0,3,5,2] : Array (Fin 6))[x.val]!
  invFun x := (#[2,1,5,3,0,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow59 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,0,1,4,5,2] : Array (Fin 6))[x.val]!
  invFun x := (#[1,2,5,0,3,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow60 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,1,2,4,0,3] : Array (Fin 6))[x.val]!
  invFun x := (#[4,1,2,5,3,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow61 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,2,1,5,0,3] : Array (Fin 6))[x.val]!
  invFun x := (#[4,2,1,5,0,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow62 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,5,0,2,1,3] : Array (Fin 6))[x.val]!
  invFun x := (#[2,4,3,5,0,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow63 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,0,5,4,1,3] : Array (Fin 6))[x.val]!
  invFun x := (#[1,4,0,5,3,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow64 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,4,0,1,2,3] : Array (Fin 6))[x.val]!
  invFun x := (#[2,3,4,5,1,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow65 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,0,4,5,2,3] : Array (Fin 6))[x.val]!
  invFun x := (#[1,0,4,5,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow66 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,5,2,0,4,3] : Array (Fin 6))[x.val]!
  invFun x := (#[3,0,2,5,4,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow67 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,2,5,1,4,3] : Array (Fin 6))[x.val]!
  invFun x := (#[0,3,1,5,4,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow68 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,4,1,0,5,3] : Array (Fin 6))[x.val]!
  invFun x := (#[3,2,0,5,1,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow69 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,1,4,2,5,3] : Array (Fin 6))[x.val]!
  invFun x := (#[0,1,3,5,2,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow70 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,5,4,1,0,3] : Array (Fin 6))[x.val]!
  invFun x := (#[4,3,0,5,2,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow71 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,4,5,2,0,3] : Array (Fin 6))[x.val]!
  invFun x := (#[4,0,3,5,1,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow72 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,2,4,0,1,3] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,1,5,2,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow73 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,4,2,5,1,3] : Array (Fin 6))[x.val]!
  invFun x := (#[0,4,2,5,1,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow74 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,1,5,0,2,3] : Array (Fin 6))[x.val]!
  invFun x := (#[3,1,4,5,0,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow75 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,5,1,4,2,3] : Array (Fin 6))[x.val]!
  invFun x := (#[0,2,4,5,3,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow76 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,0,1,2,4,3] : Array (Fin 6))[x.val]!
  invFun x := (#[1,2,3,5,4,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow77 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,1,0,5,4,3] : Array (Fin 6))[x.val]!
  invFun x := (#[2,1,0,5,4,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow78 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,0,2,1,5,3] : Array (Fin 6))[x.val]!
  invFun x := (#[1,3,2,5,0,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow79 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,2,0,4,5,3] : Array (Fin 6))[x.val]!
  invFun x := (#[2,0,1,5,3,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow80 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,2,3,1,0,4] : Array (Fin 6))[x.val]!
  invFun x := (#[4,3,1,2,5,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow81 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,3,2,5,0,4] : Array (Fin 6))[x.val]!
  invFun x := (#[4,0,2,1,5,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow82 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,5,3,0,1,4] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,0,2,5,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow83 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,3,5,2,1,4] : Array (Fin 6))[x.val]!
  invFun x := (#[0,4,3,1,5,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow84 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,0,5,1,2,4] : Array (Fin 6))[x.val]!
  invFun x := (#[1,3,4,0,5,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow85 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,5,0,3,2,4] : Array (Fin 6))[x.val]!
  invFun x := (#[2,0,4,3,5,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow86 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,1,0,2,3,4] : Array (Fin 6))[x.val]!
  invFun x := (#[2,1,3,4,5,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow87 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,0,1,5,3,4] : Array (Fin 6))[x.val]!
  invFun x := (#[1,2,0,4,5,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow88 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,1,2,0,5,4] : Array (Fin 6))[x.val]!
  invFun x := (#[3,1,2,0,5,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow89 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,2,1,3,5,4] : Array (Fin 6))[x.val]!
  invFun x := (#[0,2,1,3,5,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow90 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,5,1,2,0,4] : Array (Fin 6))[x.val]!
  invFun x := (#[4,2,3,0,5,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow91 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,1,5,3,0,4] : Array (Fin 6))[x.val]!
  invFun x := (#[4,1,0,3,5,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow92 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,0,2,3,1,4] : Array (Fin 6))[x.val]!
  invFun x := (#[1,4,2,3,5,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow93 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,2,0,5,1,4] : Array (Fin 6))[x.val]!
  invFun x := (#[2,4,1,0,5,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow94 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,3,1,0,2,4] : Array (Fin 6))[x.val]!
  invFun x := (#[3,2,4,1,5,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow95 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,1,3,5,2,4] : Array (Fin 6))[x.val]!
  invFun x := (#[0,1,4,2,5,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow96 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,2,5,0,3,4] : Array (Fin 6))[x.val]!
  invFun x := (#[3,0,1,4,5,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow97 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,5,2,1,3,4] : Array (Fin 6))[x.val]!
  invFun x := (#[0,3,2,4,5,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow98 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,0,1,5,4] : Array (Fin 6))[x.val]!
  invFun x := (#[2,3,0,1,5,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow99 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,0,3,2,5,4] : Array (Fin 6))[x.val]!
  invFun x := (#[1,0,3,2,5,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow100 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,2,1,0,5] : Array (Fin 6))[x.val]!
  invFun x := (#[4,3,2,0,1,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow101 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,2,4,3,0,5] : Array (Fin 6))[x.val]!
  invFun x := (#[4,0,1,3,2,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow102 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,3,2,0,1,5] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,2,1,0,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow103 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,2,3,4,1,5] : Array (Fin 6))[x.val]!
  invFun x := (#[0,4,1,2,3,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow104 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,0,1,3,2,5] : Array (Fin 6))[x.val]!
  invFun x := (#[1,2,4,3,0,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow105 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,1,0,4,2,5] : Array (Fin 6))[x.val]!
  invFun x := (#[2,1,4,0,3,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow106 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,1,4,0,3,5] : Array (Fin 6))[x.val]!
  invFun x := (#[3,1,0,4,2,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow107 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,4,1,2,3,5] : Array (Fin 6))[x.val]!
  invFun x := (#[0,2,3,4,1,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow108 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,0,3,1,4,5] : Array (Fin 6))[x.val]!
  invFun x := (#[1,3,0,2,4,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow109 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,3,0,2,4,5] : Array (Fin 6))[x.val]!
  invFun x := (#[2,0,3,1,4,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow110 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,1,3,2,0,5] : Array (Fin 6))[x.val]!
  invFun x := (#[4,1,3,2,0,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow111 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,1,4,0,5] : Array (Fin 6))[x.val]!
  invFun x := (#[4,2,0,1,3,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow112 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,0,4,2,1,5] : Array (Fin 6))[x.val]!
  invFun x := (#[1,4,3,0,2,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow113 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,4,0,3,1,5] : Array (Fin 6))[x.val]!
  invFun x := (#[2,4,0,3,1,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow114 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,4,3,0,2,5] : Array (Fin 6))[x.val]!
  invFun x := (#[3,0,4,2,1,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow115 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,3,4,1,2,5] : Array (Fin 6))[x.val]!
  invFun x := (#[0,3,4,1,2,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow116 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,2,0,1,3,5] : Array (Fin 6))[x.val]!
  invFun x := (#[2,3,1,4,0,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow117 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,0,2,4,3,5] : Array (Fin 6))[x.val]!
  invFun x := (#[1,0,2,4,3,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow118 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,2,1,0,4,5] : Array (Fin 6))[x.val]!
  invFun x := (#[3,2,1,0,4,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow119 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,1,2,3,4,5] : Array (Fin 6))[x.val]!
  invFun x := (#[0,1,2,3,4,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def topRows (i : Fin 120) : Equiv.Perm (Fin 6) :=
  (if i.val < 60 then (if i.val < 30 then (if i.val < 15 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then topRow0 else (if i.val < 2 then topRow1 else topRow2)) else (if i.val < 5 then (if i.val < 4 then topRow3 else topRow4) else (if i.val < 6 then topRow5 else topRow6))) else (if i.val < 11 then (if i.val < 9 then (if i.val < 8 then topRow7 else topRow8) else (if i.val < 10 then topRow9 else topRow10)) else (if i.val < 13 then (if i.val < 12 then topRow11 else topRow12) else (if i.val < 14 then topRow13 else topRow14)))) else (if i.val < 22 then (if i.val < 18 then (if i.val < 16 then topRow15 else (if i.val < 17 then topRow16 else topRow17)) else (if i.val < 20 then (if i.val < 19 then topRow18 else topRow19) else (if i.val < 21 then topRow20 else topRow21))) else (if i.val < 26 then (if i.val < 24 then (if i.val < 23 then topRow22 else topRow23) else (if i.val < 25 then topRow24 else topRow25)) else (if i.val < 28 then (if i.val < 27 then topRow26 else topRow27) else (if i.val < 29 then topRow28 else topRow29))))) else (if i.val < 45 then (if i.val < 37 then (if i.val < 33 then (if i.val < 31 then topRow30 else (if i.val < 32 then topRow31 else topRow32)) else (if i.val < 35 then (if i.val < 34 then topRow33 else topRow34) else (if i.val < 36 then topRow35 else topRow36))) else (if i.val < 41 then (if i.val < 39 then (if i.val < 38 then topRow37 else topRow38) else (if i.val < 40 then topRow39 else topRow40)) else (if i.val < 43 then (if i.val < 42 then topRow41 else topRow42) else (if i.val < 44 then topRow43 else topRow44)))) else (if i.val < 52 then (if i.val < 48 then (if i.val < 46 then topRow45 else (if i.val < 47 then topRow46 else topRow47)) else (if i.val < 50 then (if i.val < 49 then topRow48 else topRow49) else (if i.val < 51 then topRow50 else topRow51))) else (if i.val < 56 then (if i.val < 54 then (if i.val < 53 then topRow52 else topRow53) else (if i.val < 55 then topRow54 else topRow55)) else (if i.val < 58 then (if i.val < 57 then topRow56 else topRow57) else (if i.val < 59 then topRow58 else topRow59)))))) else (if i.val < 90 then (if i.val < 75 then (if i.val < 67 then (if i.val < 63 then (if i.val < 61 then topRow60 else (if i.val < 62 then topRow61 else topRow62)) else (if i.val < 65 then (if i.val < 64 then topRow63 else topRow64) else (if i.val < 66 then topRow65 else topRow66))) else (if i.val < 71 then (if i.val < 69 then (if i.val < 68 then topRow67 else topRow68) else (if i.val < 70 then topRow69 else topRow70)) else (if i.val < 73 then (if i.val < 72 then topRow71 else topRow72) else (if i.val < 74 then topRow73 else topRow74)))) else (if i.val < 82 then (if i.val < 78 then (if i.val < 76 then topRow75 else (if i.val < 77 then topRow76 else topRow77)) else (if i.val < 80 then (if i.val < 79 then topRow78 else topRow79) else (if i.val < 81 then topRow80 else topRow81))) else (if i.val < 86 then (if i.val < 84 then (if i.val < 83 then topRow82 else topRow83) else (if i.val < 85 then topRow84 else topRow85)) else (if i.val < 88 then (if i.val < 87 then topRow86 else topRow87) else (if i.val < 89 then topRow88 else topRow89))))) else (if i.val < 105 then (if i.val < 97 then (if i.val < 93 then (if i.val < 91 then topRow90 else (if i.val < 92 then topRow91 else topRow92)) else (if i.val < 95 then (if i.val < 94 then topRow93 else topRow94) else (if i.val < 96 then topRow95 else topRow96))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then topRow97 else topRow98) else (if i.val < 100 then topRow99 else topRow100)) else (if i.val < 103 then (if i.val < 102 then topRow101 else topRow102) else (if i.val < 104 then topRow103 else topRow104)))) else (if i.val < 112 then (if i.val < 108 then (if i.val < 106 then topRow105 else (if i.val < 107 then topRow106 else topRow107)) else (if i.val < 110 then (if i.val < 109 then topRow108 else topRow109) else (if i.val < 111 then topRow110 else topRow111))) else (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then topRow112 else topRow113) else (if i.val < 115 then topRow114 else topRow115)) else (if i.val < 118 then (if i.val < 117 then topRow116 else topRow117) else (if i.val < 119 then topRow118 else topRow119)))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction169ClassPilot

end
