import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1312 through 1343. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1600Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,12,13,2,3,8,9,15,14,5,4,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,13,12,3,2,8,9,14,15,4,5,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1600Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,13,12,7,6,1,0,10,11,4,5,15,14,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,10,11,5,4,14,15,8,9,3,2,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1600Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,14,15,13,12,11,10,8,9,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,14,15,12,13,10,11,8,9,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1600Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1600Generator0 else (if j.val < 2 then node1600Generator1 else node1600Generator2))

def node1601Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1601Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,1,0,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,1,0,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1601Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1601Generator0 else node1601Generator1)

def node1602Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1602Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,2,3,4,5,15,14,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,8,9,14,15,0,1,2,3,5,4,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1602Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,8,9,7,6,12,13,11,10,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,1,0,9,8,6,7,13,12,10,11,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1602Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1602Generator0 else (if j.val < 2 then node1602Generator1 else node1602Generator2))

def node1603Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,13,12,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1603Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,10,11,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,14,15,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1603Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,5,4,14,15,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,5,4,14,15,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1603Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1603Generator0 else (if j.val < 2 then node1603Generator1 else node1603Generator2))

def node1604Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,9,8,2,3,13,12,7,6,1,0,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,0,1,11,10,5,4,15,14,9,8,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1604Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,12,13,6,7,0,1,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,6,7,0,1,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1604Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,7,6,8,9,11,10,13,12,15,14,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,5,4,6,7,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1604Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1604Generator0 else (if j.val < 2 then node1604Generator1 else node1604Generator2))

def node1605Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1605Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1605Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,12,13,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,13,12,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1605Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1605Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1605Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1605Generator0 else node1605Generator1) else (if j.val < 3 then node1605Generator2 else (if j.val < 4 then node1605Generator3 else node1605Generator4)))

def node1606Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,0,1,7,6,8,9,11,10,13,12,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,7,6,8,9,11,10,13,12,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1606Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,7,6,9,8,15,14,0,1,3,2,5,4,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,3,2,5,4,14,15,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1606Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,0,1,13,12,6,7,8,9,10,11,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,8,9,10,11,12,13,7,6,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1606Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1606Generator0 else (if j.val < 2 then node1606Generator1 else node1606Generator2))

def node1607Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,1,0,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,0,1,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1607Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,6,7,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,8,9,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1607Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1607Generator0 else node1607Generator1)

def node1608Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,13,12,7,6,9,8,11,10,5,4,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,11,10,5,4,7,6,9,8,3,2,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1608Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,1,0,10,11,4,5,15,14,8,9,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,8,9,2,3,12,13,6,7,0,1,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1608Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,0,1,10,11,4,5,7,6,8,9,2,3,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,12,13,6,7,9,8,10,11,4,5,15,14,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1608Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1608Generator0 else (if j.val < 2 then node1608Generator1 else node1608Generator2))

def node1609Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1609Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1609Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1609Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1609Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1609Generator0 else node1609Generator1) else (if j.val < 3 then node1609Generator2 else node1609Generator3))

def node1610Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,4,5,7,6,1,0,3,2,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,6,7,9,8,2,3,5,4,14,15,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1610Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,7,6,9,8,2,3,5,4,15,14,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,9,8,3,2,5,4,14,15,0,1,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1610Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,8,9,2,3,5,4,14,15,1,0,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,9,8,2,3,4,5,15,14,0,1,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1610Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1610Generator0 else (if j.val < 2 then node1610Generator1 else node1610Generator2))

def node1611Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,7,6,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,9,8,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1611Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1611Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,7,6,0,1,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,3,2,5,4,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1611Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1611Generator0 else (if j.val < 2 then node1611Generator1 else node1611Generator2))

def node1612Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,4,5,2,3,10,11,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,4,5,3,2,11,10,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1612Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,12,13,11,10,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,9,8,0,1,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1612Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1612Generator0 else node1612Generator1)

def node1613Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,9,8,1,0,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,11,10,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1613Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,9,8,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1613Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,9,8,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1613Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1613Generator0 else (if j.val < 2 then node1613Generator1 else node1613Generator2))

def node1614Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,11,10,12,13,6,7,8,9,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,10,11,12,13,7,6,8,9,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1614Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,9,8,2,3,4,5,15,14,1,0,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,8,9,2,3,5,4,15,14,0,1,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1614Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,8,9,11,10,13,12,6,7,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,12,13,6,7,9,8,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1614Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1614Generator0 else (if j.val < 2 then node1614Generator1 else node1614Generator2))

def node1615Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1615Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,9,8,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1615Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1615Generator0 else node1615Generator1)

def node1616Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1616Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,8,9,10,11,12,13,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,12,13,6,7,8,9,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1616Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,13,12,6,7,0,1,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,6,7,0,1,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1616Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1616Generator0 else (if j.val < 2 then node1616Generator1 else node1616Generator2))

def node1617Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1617Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,5,4,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,4,5,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1617Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,12,13,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,13,12,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1617Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1617Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1617Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1617Generator0 else node1617Generator1) else (if j.val < 3 then node1617Generator2 else (if j.val < 4 then node1617Generator3 else node1617Generator4)))

def node1618Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,0,1,6,7,14,15,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,1,0,6,7,15,14,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1618Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,8,9,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1618Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1618Generator0 else node1618Generator1)

def node1619Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,13,12,2,3,9,8,15,14,5,4,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,13,12,2,3,9,8,14,15,5,4,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1619Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,14,15,12,13,10,11,8,9,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,14,15,13,12,11,10,8,9,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1619Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,8,9,11,10,12,13,15,14,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,4,5,6,7,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1619Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1619Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1619Generator0 else node1619Generator1) else (if j.val < 3 then node1619Generator2 else node1619Generator3))

def node1620Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,4,5,10,11,0,1,7,6,13,12,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,4,5,11,10,1,0,6,7,13,12,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1620Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,14,15,12,13,10,11,9,8,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,15,14,13,12,11,10,9,8,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1620Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,0,1,2,3,5,4,7,6,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,7,6,9,8,10,11,13,12,15,14,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1620Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1620Generator0 else (if j.val < 2 then node1620Generator1 else node1620Generator2))

def node1621Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,0,1,2,3,4,5,7,6,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,8,9,10,11,13,12,14,15,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1621Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,8,9,3,2,5,4,14,15,1,0,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,5,4,7,6,1,0,2,3,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1621Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,7,6,1,0,11,10,5,4,15,14,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,9,8,3,2,12,13,7,6,1,0,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1621Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1621Generator0 else (if j.val < 2 then node1621Generator1 else node1621Generator2))

def node1622Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,10,11,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1622Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1622Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,5,4,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,14,15,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1622Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1622Generator0 else (if j.val < 2 then node1622Generator1 else node1622Generator2))

def node1623Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1623Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1623Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1623Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1623Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1623Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1623Generator0 else node1623Generator1) else (if j.val < 3 then node1623Generator2 else (if j.val < 4 then node1623Generator3 else node1623Generator4)))

def node1624Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1624Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1624Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1624Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1624Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1624Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1624Generator0 else node1624Generator1) else (if j.val < 3 then node1624Generator2 else (if j.val < 4 then node1624Generator3 else node1624Generator4)))

def node1625Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,12,13,2,3,8,9,15,14,5,4,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,13,12,3,2,8,9,14,15,4,5,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1625Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,14,15,13,12,11,10,8,9,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,15,14,12,13,11,10,8,9,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1625Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,8,9,11,10,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,5,4,6,7,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1625Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1625Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1625Generator0 else node1625Generator1) else (if j.val < 3 then node1625Generator2 else node1625Generator3))

def node1626Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,9,8,7,6,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,9,8,7,6,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1626Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,4,5,2,3,6,7,8,9,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,4,5,2,3,6,7,8,9,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1626Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1626Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1626Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,3,2,6,7,9,8,10,11,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,6,7,9,8,10,11,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1626Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1626Generator0 else node1626Generator1) else (if j.val < 3 then node1626Generator2 else (if j.val < 4 then node1626Generator3 else node1626Generator4)))

def node1627Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,3,2,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,2,3,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1627Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,8,9,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1627Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1627Generator0 else node1627Generator1)

def node1628Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1628Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,10,11,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,11,10,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1628Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,2,3,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,3,2,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1628Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1628Generator0 else (if j.val < 2 then node1628Generator1 else node1628Generator2))

def node1629Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1629Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,5,4,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1629Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1629Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1629Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1629Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1629Generator0 else node1629Generator1) else (if j.val < 3 then node1629Generator2 else (if j.val < 4 then node1629Generator3 else node1629Generator4)))

def node1630Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,12,13,6,7,9,8,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,8,9,11,10,13,12,6,7,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1630Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1630Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1630Generator0 else node1630Generator1)

def node1631Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,11,10,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,10,11,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1631Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,14,15,13,12,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,10,11,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1631Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,11,10,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,13,12,4,5,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1631Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1631Generator0 else (if j.val < 2 then node1631Generator1 else node1631Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
