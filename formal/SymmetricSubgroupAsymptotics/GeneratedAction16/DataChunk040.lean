import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1280 through 1311. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1568Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,8,9,11,10,15,14,5,4,2,3,0,1,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,1,0,2,3,5,4,15,14,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1568Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,14,15,4,5,13,12,7,6,9,8,11,10,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,14,15,4,5,9,8,11,10,13,12,7,6,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1568Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,6,7,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,8,9,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1568Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1568Generator0 else (if j.val < 2 then node1568Generator1 else node1568Generator2))

def node1569Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1569Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1569Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1569Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1569Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1569Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1569Generator0 else node1569Generator1) else (if j.val < 3 then node1569Generator2 else (if j.val < 4 then node1569Generator3 else node1569Generator4)))

def node1570Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,9,8,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,8,9,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1570Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,7,6,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,7,6,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1570Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1570Generator0 else node1570Generator1)

def node1571Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1571Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,12,13,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,13,12,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1571Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1571Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1571Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1571Generator0 else node1571Generator1) else (if j.val < 3 then node1571Generator2 else node1571Generator3))

def node1572Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1572Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,4,5,2,3,15,14,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,4,5,3,2,10,11,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1572Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,10,11,13,12,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,15,14,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1572Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1572Generator0 else (if j.val < 2 then node1572Generator1 else node1572Generator2))

def node1573Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,1,0,2,3,12,13,6,7,9,8,11,10,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,14,15,8,9,11,10,13,12,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1573Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,6,7,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,6,7,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1573Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,9,8,2,3,13,12,15,14,1,0,10,11,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,4,5,14,15,1,0,3,2,12,13,7,6,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1573Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1573Generator0 else (if j.val < 2 then node1573Generator1 else node1573Generator2))

def node1574Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,1,0,2,3,14,15,12,13,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,15,14,13,12,1,0,2,3,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1574Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,12,13,14,15,0,1,2,3,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,3,2,1,0,13,12,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1574Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,3,2,0,1,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,3,2,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1574Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1574Generator0 else (if j.val < 2 then node1574Generator1 else node1574Generator2))

def node1575Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1575Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,8,9,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1575Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1575Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1575Generator0 else (if j.val < 2 then node1575Generator1 else node1575Generator2))

def node1576Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,9,8,4,5,2,3,1,0,15,14,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,6,7,2,3,5,4,15,14,1,0,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1576Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,15,14,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1576Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,10,11,12,13,6,7,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,10,11,13,12,6,7,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1576Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1576Generator0 else (if j.val < 2 then node1576Generator1 else node1576Generator2))

def node1577Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1577Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,9,8,10,11,12,13,14,15,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,2,3,5,4,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1577Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,10,11,8,9,14,15,12,13,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,3,2,0,1,6,7,4,5,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1577Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,13,12,6,7,0,1,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,6,7,0,1,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1577Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1577Generator0 else node1577Generator1) else (if j.val < 3 then node1577Generator2 else node1577Generator3))

def node1578Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,0,1,3,2,5,4,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,7,6,1,0,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1578Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1578Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,1,0,8,9,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,0,1,8,9,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1578Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1578Generator0 else (if j.val < 2 then node1578Generator1 else node1578Generator2))

def node1579Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1579Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,1,0,9,8,14,15,12,13,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,1,0,2,3,5,4,9,8,14,15,12,13,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1579Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,1,0,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,1,0,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1579Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1579Generator0 else (if j.val < 2 then node1579Generator1 else node1579Generator2))

def node1580Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1580Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1580Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1580Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1580Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1580Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1580Generator0 else node1580Generator1) else (if j.val < 3 then node1580Generator2 else (if j.val < 4 then node1580Generator3 else node1580Generator4)))

def node1581Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,8,9,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,6,7,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1581Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1581Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1581Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,11,10,13,12,7,6,9,8,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,11,10,13,12,7,6,9,8,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1581Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1581Generator0 else node1581Generator1) else (if j.val < 3 then node1581Generator2 else node1581Generator3))

def node1582Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,4,5,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,4,5,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1582Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1582Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,15,14,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,8,9,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1582Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1582Generator0 else (if j.val < 2 then node1582Generator1 else node1582Generator2))

def node1583Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1583Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,14,15,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,8,9,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1583Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,4,5,2,3,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,4,5,2,3,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1583Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1583Generator0 else (if j.val < 2 then node1583Generator1 else node1583Generator2))

def node1584Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,15,14,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,13,12,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1584Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,14,15,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,9,8,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1584Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,13,12,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,10,11,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1584Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1584Generator0 else (if j.val < 2 then node1584Generator1 else node1584Generator2))

def node1585Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,10,11,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,5,4,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1585Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,3,2,13,12,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,3,2,13,12,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1585Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,6,7,12,13,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,6,7,13,12,10,11,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1585Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1585Generator0 else (if j.val < 2 then node1585Generator1 else node1585Generator2))

def node1586Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1586Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1586Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1586Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1586Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1586Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1586Generator0 else node1586Generator1) else (if j.val < 3 then node1586Generator2 else (if j.val < 4 then node1586Generator3 else node1586Generator4)))

def node1587Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,15,14,4,5,12,13,7,6,9,8,10,11,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,15,14,4,5,9,8,11,10,12,13,6,7,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1587Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1587Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,0,1,8,9,10,11,12,13,7,6,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,1,0,13,12,6,7,8,9,10,11,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1587Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1587Generator0 else (if j.val < 2 then node1587Generator1 else node1587Generator2))

def node1588Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1588Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1588Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1588Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1588Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1588Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1588Generator0 else node1588Generator1) else (if j.val < 3 then node1588Generator2 else (if j.val < 4 then node1588Generator3 else node1588Generator4)))

def node1589Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,4,5,7,6,11,10,8,9,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,4,5,7,6,10,11,9,8,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1589Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1589Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,12,13,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,0,1,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1589Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1589Generator0 else (if j.val < 2 then node1589Generator1 else node1589Generator2))

def node1590Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1590Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,8,9,6,7,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,8,9,6,7,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1590Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,10,11,12,13,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,10,11,12,13,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1590Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1590Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,6,7,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,8,9,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1590Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1590Generator0 else node1590Generator1) else (if j.val < 3 then node1590Generator2 else (if j.val < 4 then node1590Generator3 else node1590Generator4)))

def node1591Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,9,8,7,6,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,9,8,7,6,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1591Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1591Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,5,4,2,3,11,10,13,12,7,6,8,9,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,3,2,11,10,12,13,7,6,9,8,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1591Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,3,2,6,7,9,8,10,11,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,6,7,9,8,10,11,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1591Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1591Generator0 else node1591Generator1) else (if j.val < 3 then node1591Generator2 else node1591Generator3))

def node1592Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,12,13,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1592Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,3,2,11,10,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,2,3,10,11,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1592Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,5,4,2,3,13,12,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,5,4,2,3,12,13,11,10,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1592Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1592Generator0 else (if j.val < 2 then node1592Generator1 else node1592Generator2))

def node1593Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1593Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1593Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1593Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1593Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1593Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1593Generator0 else node1593Generator1) else (if j.val < 3 then node1593Generator2 else (if j.val < 4 then node1593Generator3 else node1593Generator4)))

def node1594Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,4,5,15,14,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,4,5,10,11,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1594Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,0,1,15,14,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,0,1,10,11,13,12,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1594Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,15,14,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,4,5,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1594Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1594Generator0 else (if j.val < 2 then node1594Generator1 else node1594Generator2))

def node1595Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,5,4,6,7,8,9,3,2,12,13,14,15,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,3,2,4,5,6,7,1,0,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1595Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,1,0,2,3,12,13,6,7,9,8,10,11,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,15,14,8,9,11,10,12,13,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1595Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,1,0,2,3,4,5,7,6,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,8,9,11,10,13,12,15,14,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1595Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1595Generator0 else (if j.val < 2 then node1595Generator1 else node1595Generator2))

def node1596Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,5,4,2,3,13,12,11,10,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,5,4,2,3,13,12,11,10,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1596Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,9,8,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1596Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,3,2,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,6,7,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1596Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1596Generator0 else (if j.val < 2 then node1596Generator1 else node1596Generator2))

def node1597Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1597Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1597Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1597Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1597Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1597Generator0 else node1597Generator1) else (if j.val < 3 then node1597Generator2 else node1597Generator3))

def node1598Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,15,14,6,7,13,12,10,11,8,9,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,6,7,12,13,10,11,9,8,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1598Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,6,7,3,2,0,1,14,15,5,4,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,7,6,13,12,4,5,14,15,0,1,2,3,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1598Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1598Generator0 else node1598Generator1)

def node1599Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,4,5,2,3,1,0,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,6,7,5,4,2,3,1,0,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1599Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,7,6,12,13,1,0,3,2,5,4,14,15,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,9,8,11,10,3,2,0,1,15,14,4,5,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1599Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1599Generator0 else node1599Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
