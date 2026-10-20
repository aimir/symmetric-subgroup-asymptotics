import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1248 through 1279. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1481Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,8,9,4,5,2,3,0,1,15,14,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,2,3,4,5,15,14,1,0,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1481Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,8,9,6,7,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,8,9,6,7,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1481Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,10,11,12,13,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1481Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1481Generator0 else (if j.val < 2 then node1481Generator1 else node1481Generator2))

def node1482Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1482Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,14,15,12,13,2,3,0,1,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,0,1,2,3,15,14,12,13,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1482Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1482Generator0 else node1482Generator1)

def node1483Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,3,2,1,0,7,6,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,10,11,9,8,12,13,14,15,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1483Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,15,14,13,12,10,11,8,9,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,15,14,13,12,10,11,8,9,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1483Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1483Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1483Generator0 else (if j.val < 2 then node1483Generator1 else node1483Generator2))

def node1484Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,15,14,8,9,10,11,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1484Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,12,13,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1484Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,6,7,12,13,14,15,5,4,2,3,0,1,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,2,3,1,0,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1484Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1484Generator0 else (if j.val < 2 then node1484Generator1 else node1484Generator2))

def node1485Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,14,15,1,0,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,11,10,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1485Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,10,11,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,8,9,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1485Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1485Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1485Generator0 else (if j.val < 2 then node1485Generator1 else node1485Generator2))

def node1486Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,9,8,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,9,8,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1486Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,11,10,9,8,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1486Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,10,11,13,12,15,14,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,0,1,2,3,4,5,7,6,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1486Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1486Generator0 else (if j.val < 2 then node1486Generator1 else node1486Generator2))

def node1487Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,12,13,2,3,8,9,15,14,4,5,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,12,13,3,2,8,9,14,15,4,5,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1487Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,0,1,3,2,5,4,6,7,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,7,6,8,9,11,10,13,12,15,14,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1487Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1487Generator0 else node1487Generator1)

def node1488Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,14,15,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,15,14,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1488Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,15,14,12,13,11,10,8,9,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,15,14,12,13,10,11,9,8,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1488Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,11,10,8,9,14,15,13,12,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,2,3,1,0,6,7,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1488Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1488Generator0 else (if j.val < 2 then node1488Generator1 else node1488Generator2))

def node1489Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,1,0,6,7,13,12,2,3,9,8,15,14,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,8,9,15,14,4,5,11,10,1,0,7,6,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1489Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,8,9,10,11,13,12,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,1,0,3,2,4,5,6,7,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1489Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,3,2,8,9,14,15,4,5,10,11,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,3,2,8,9,15,14,4,5,10,11,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1489Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1489Generator0 else (if j.val < 2 then node1489Generator1 else node1489Generator2))

def node1490Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,6,7,5,4,2,3,0,1,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,7,6,4,5,3,2,1,0,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1490Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,1,0,2,3,5,4,7,6,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,7,6,9,8,11,10,12,13,14,15,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1490Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1490Generator0 else node1490Generator1)

def node1491Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1491Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,4,5,10,11,0,1,6,7,12,13,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,4,5,10,11,0,1,6,7,12,13,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1491Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,0,1,6,7,12,13,2,3,8,9,14,15,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,8,9,15,14,4,5,10,11,1,0,6,7,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1491Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1491Generator0 else (if j.val < 2 then node1491Generator1 else node1491Generator2))

def node1547Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,9,8,7,6,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,9,8,7,6,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1547Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,4,5,2,3,7,6,9,8,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,4,5,2,3,7,6,9,8,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1547Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1547Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1547Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1547Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,3,2,6,7,9,8,10,11,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,6,7,9,8,10,11,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1547Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node1547Generator0 else (if j.val < 2 then node1547Generator1 else node1547Generator2)) else (if j.val < 4 then node1547Generator3 else (if j.val < 5 then node1547Generator4 else node1547Generator5)))

def node1548Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,9,8,7,6,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,9,8,7,6,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1548Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,4,5,2,3,7,6,9,8,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,4,5,2,3,7,6,9,8,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1548Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1548Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1548Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,3,2,6,7,9,8,10,11,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,6,7,9,8,10,11,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1548Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1548Generator0 else node1548Generator1) else (if j.val < 3 then node1548Generator2 else (if j.val < 4 then node1548Generator3 else node1548Generator4)))

def node1549Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,3,2,9,8,7,6,5,4,11,10,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,11,10,9,8,7,6,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1549Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1549Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,8,9,15,14,12,13,10,11,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,0,1,15,14,12,13,2,3,8,9,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1549Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1549Generator0 else (if j.val < 2 then node1549Generator1 else node1549Generator2))

def node1550Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,13,12,14,15,8,9,11,10,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,12,13,15,14,8,9,11,10,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1550Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,4,5,15,14,9,8,2,3,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,10,11,4,5,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1550Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1550Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,9,8,14,15,12,13,11,10,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,3,2,0,1,7,6,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1550Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,6,7,1,0,2,3,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,5,4,6,7,1,0,3,2,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1550Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1550Generator0 else node1550Generator1) else (if j.val < 3 then node1550Generator2 else (if j.val < 4 then node1550Generator3 else node1550Generator4)))

def node1551Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,13,12,14,15,8,9,11,10,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,12,13,15,14,8,9,11,10,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1551Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1551Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,8,9,15,14,13,12,11,10,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,3,2,0,1,6,7,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1551Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,6,7,1,0,2,3,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,5,4,6,7,1,0,3,2,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1551Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1551Generator0 else node1551Generator1) else (if j.val < 3 then node1551Generator2 else node1551Generator3))

def node1552Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1552Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1552Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,5,4,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,7,6,5,4,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1552Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1552Generator0 else (if j.val < 2 then node1552Generator1 else node1552Generator2))

def node1553Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1553Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1553Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1553Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1553Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1553Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1553Generator0 else node1553Generator1) else (if j.val < 3 then node1553Generator2 else (if j.val < 4 then node1553Generator3 else node1553Generator4)))

def node1554Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,0,1,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,0,1,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1554Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,9,8,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,11,10,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1554Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1554Generator0 else node1554Generator1)

def node1555Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1555Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1555Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1555Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1555Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1555Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1555Generator0 else node1555Generator1) else (if j.val < 3 then node1555Generator2 else (if j.val < 4 then node1555Generator3 else node1555Generator4)))

def node1556Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1556Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1556Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1556Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,13,12,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1556Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1556Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1556Generator0 else node1556Generator1) else (if j.val < 3 then node1556Generator2 else (if j.val < 4 then node1556Generator3 else node1556Generator4)))

def node1557Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,8,9,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,6,7,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1557Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,4,5,2,3,7,6,9,8,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,4,5,2,3,7,6,9,8,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1557Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1557Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1557Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,6,7,8,9,11,10,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,6,7,8,9,11,10,13,12,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1557Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1557Generator0 else node1557Generator1) else (if j.val < 3 then node1557Generator2 else (if j.val < 4 then node1557Generator3 else node1557Generator4)))

def node1558Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1558Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1558Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1558Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1558Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1558Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1558Generator0 else node1558Generator1) else (if j.val < 3 then node1558Generator2 else (if j.val < 4 then node1558Generator3 else node1558Generator4)))

def node1559Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,7,6,5,4,11,10,9,8,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,7,6,5,4,11,10,9,8,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1559Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,0,1,3,2,12,13,14,15,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,13,12,15,14,2,3,1,0,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1559Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1559Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1559Generator0 else (if j.val < 2 then node1559Generator1 else node1559Generator2))

def node1560Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1560Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1560Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,5,4,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,4,5,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1560Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1560Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1560Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1560Generator0 else node1560Generator1) else (if j.val < 3 then node1560Generator2 else (if j.val < 4 then node1560Generator3 else node1560Generator4)))

def node1561Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,1,0,15,14,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,2,3,12,13,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1561Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,14,15,13,12,3,2,0,1,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,0,1,3,2,14,15,12,13,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1561Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1561Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1561Generator0 else (if j.val < 2 then node1561Generator1 else node1561Generator2))

def node1562Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1562Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,5,4,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,4,5,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1562Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1562Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1562Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1562Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1562Generator0 else node1562Generator1) else (if j.val < 3 then node1562Generator2 else (if j.val < 4 then node1562Generator3 else node1562Generator4)))

def node1563Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1563Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1563Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1563Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,13,12,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1563Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1563Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1563Generator0 else node1563Generator1) else (if j.val < 3 then node1563Generator2 else (if j.val < 4 then node1563Generator3 else node1563Generator4)))

def node1564Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1564Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1564Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,5,4,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,4,5,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1564Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1564Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1564Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1564Generator0 else node1564Generator1) else (if j.val < 3 then node1564Generator2 else (if j.val < 4 then node1564Generator3 else node1564Generator4)))

def node1565Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1565Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,1,0,7,6,14,15,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,1,0,7,6,11,10,12,13,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1565Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1565Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1565Generator0 else (if j.val < 2 then node1565Generator1 else node1565Generator2))

def node1566Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1566Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,5,4,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,4,5,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1566Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1566Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1566Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1566Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1566Generator0 else node1566Generator1) else (if j.val < 3 then node1566Generator2 else (if j.val < 4 then node1566Generator3 else node1566Generator4)))

def node1567Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1567Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1567Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1567Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1567Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1567Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1567Generator0 else node1567Generator1) else (if j.val < 3 then node1567Generator2 else (if j.val < 4 then node1567Generator3 else node1567Generator4)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
