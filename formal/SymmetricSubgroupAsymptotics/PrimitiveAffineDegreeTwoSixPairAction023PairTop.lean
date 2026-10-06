import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassBase
import Mathlib.Tactic.FinCases

/-!
# Selected six-pair action 23: pair-top action

This is a resource-bounded split of the selected action-23 certificate.
All finite equations remain kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassPilot

private def topRow0 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,5,3,4,2,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,0,4,2,3,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow1 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,2,3,1,5,0] : Array (Fin 6))[x.val]!
  invFun x := (#[5,3,1,2,0,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow2 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,3,4,5,0,1] : Array (Fin 6))[x.val]!
  invFun x := (#[4,5,0,1,2,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow3 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,0,4,2,3,1] : Array (Fin 6))[x.val]!
  invFun x := (#[1,5,3,4,2,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow4 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,1,5,0,4,2] : Array (Fin 6))[x.val]!
  invFun x := (#[3,1,5,0,4,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow5 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,4,5,3,1,2] : Array (Fin 6))[x.val]!
  invFun x := (#[0,4,5,3,1,2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow6 : Equiv.Perm (Fin 6) where
  toFun x := (#[1,2,0,4,5,3] : Array (Fin 6))[x.val]!
  invFun x := (#[2,0,1,5,3,4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow7 : Equiv.Perm (Fin 6) where
  toFun x := (#[4,5,0,1,2,3] : Array (Fin 6))[x.val]!
  invFun x := (#[2,3,4,5,0,1] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow8 : Equiv.Perm (Fin 6) where
  toFun x := (#[2,0,1,5,3,4] : Array (Fin 6))[x.val]!
  invFun x := (#[1,2,0,4,5,3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow9 : Equiv.Perm (Fin 6) where
  toFun x := (#[5,3,1,2,0,4] : Array (Fin 6))[x.val]!
  invFun x := (#[4,2,3,1,5,0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow10 : Equiv.Perm (Fin 6) where
  toFun x := (#[3,4,2,0,1,5] : Array (Fin 6))[x.val]!
  invFun x := (#[3,4,2,0,1,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRow11 : Equiv.Perm (Fin 6) where
  toFun x := (#[0,1,2,3,4,5] : Array (Fin 6))[x.val]!
  invFun x := (#[0,1,2,3,4,5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topRows (i : Fin 12) : Equiv.Perm (Fin 6) :=
  (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then topRow0 else (if i.val < 2 then topRow1 else topRow2)) else (if i.val < 4 then topRow3 else (if i.val < 5 then topRow4 else topRow5))) else (if i.val < 9 then (if i.val < 7 then topRow6 else (if i.val < 8 then topRow7 else topRow8)) else (if i.val < 10 then topRow9 else (if i.val < 11 then topRow10 else topRow11))))

/-- The executable six-block action of the literal row group. -/
def pairTop : Source →* Equiv.Perm (Fin 6) where
  toFun x := topRows x.index
  map_one' := by decide +kernel
  map_mul' := by
    rintro ⟨i⟩ ⟨j⟩
    apply Equiv.ext
    intro p
    fin_cases i <;> fin_cases j <;> fin_cases p <;> decide +kernel
end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023ClassPilot

end
