import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1344 through 1375. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1632Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,5,4,14,15,0,1,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,5,4,14,15,1,0,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1632Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,4,5,15,14,0,1,10,11,12,13,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,4,5,15,14,1,0,10,11,12,13,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1632Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,0,1,11,10,13,12,6,7,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,12,13,15,14,9,8,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1632Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1632Generator0 else (if j.val < 2 then node1632Generator1 else node1632Generator2))

def node1633Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,8,9,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,6,7,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1633Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,14,15,2,3,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1633Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,0,1,6,7,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,1,0,6,7,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1633Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1633Generator0 else (if j.val < 2 then node1633Generator1 else node1633Generator2))

def node1634Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1634Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1634Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,5,4,2,3,15,14,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,5,4,2,3,10,11,13,12,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1634Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1634Generator0 else (if j.val < 2 then node1634Generator1 else node1634Generator2))

def node1635Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,7,6,8,9,15,14,1,0,3,2,4,5,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,3,2,4,5,15,14,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1635Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,4,5,14,15,0,1,2,3,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,6,7,14,15,1,0,2,3,5,4,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1635Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1635Generator0 else node1635Generator1)

def node1636Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,0,1,2,3,13,12,15,14,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,12,13,15,14,0,1,2,3,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1636Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,1,0,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1636Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,9,8,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,8,9,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1636Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1636Generator0 else (if j.val < 2 then node1636Generator1 else node1636Generator2))

def node1637Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,13,12,15,14,0,1,3,2,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,0,1,2,3,15,14,13,12,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1637Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,11,10,6,7,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,8,9,4,5,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1637Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,15,14,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1637Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1637Generator0 else (if j.val < 2 then node1637Generator1 else node1637Generator2))

def node1638Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,6,7,4,5,2,3,0,1,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,6,7,5,4,2,3,0,1,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1638Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,6,7,9,8,10,11,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,3,2,4,5,7,6,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1638Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1638Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1638Generator0 else (if j.val < 2 then node1638Generator1 else node1638Generator2))

def node1639Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,9,8,11,10,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,4,5,7,6,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1639Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,10,11,4,5,14,15,8,9,3,2,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,11,10,4,5,14,15,8,9,2,3,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1639Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,2,3,9,8,15,14,5,4,10,11,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,2,3,9,8,14,15,5,4,10,11,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1639Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1639Generator0 else (if j.val < 2 then node1639Generator1 else node1639Generator2))

def node1640Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,14,15,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,14,15,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1640Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,3,2,0,1,13,12,14,15,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,14,15,12,13,1,0,2,3,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1640Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,8,9,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,10,11,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1640Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1640Generator0 else (if j.val < 2 then node1640Generator1 else node1640Generator2))

def node1641Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,10,11,8,9,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,10,11,8,9,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1641Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,0,1,3,2,14,15,12,13,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,13,12,14,15,0,1,3,2,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1641Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,2,3,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,1,0,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1641Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1641Generator0 else (if j.val < 2 then node1641Generator1 else node1641Generator2))

def node1642Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,13,12,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,13,12,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1642Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,5,4,6,7,11,10,8,9,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,5,4,6,7,10,11,9,8,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1642Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1642Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1642Generator0 else (if j.val < 2 then node1642Generator1 else node1642Generator2))

def node1643Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,9,8,14,15,4,5,11,10,0,1,6,7,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,0,1,6,7,12,13,3,2,9,8,14,15,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1643Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,9,8,10,11,13,12,14,15,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,4,5,7,6,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1643Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,9,8,15,14,5,4,11,10,1,0,6,7,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,1,0,7,6,12,13,3,2,9,8,15,14,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1643Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1643Generator0 else (if j.val < 2 then node1643Generator1 else node1643Generator2))

def node1644Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,8,9,10,11,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,10,11,8,9,4,5,6,7,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1644Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,7,6,4,5,10,11,8,9,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,6,7,5,4,10,11,8,9,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1644Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,14,15,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1644Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1644Generator0 else (if j.val < 2 then node1644Generator1 else node1644Generator2))

def node1645Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,8,9,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1645Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,7,6,5,4,3,2,1,0,14,15,12,13,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,7,6,5,4,3,2,0,1,15,14,12,13,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1645Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,11,10,0,1,7,6,12,13,2,3,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,10,11,0,1,7,6,13,12,3,2,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1645Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1645Generator0 else (if j.val < 2 then node1645Generator1 else node1645Generator2))

def node1646Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,11,10,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,10,11,8,9,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1646Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1646Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,9,8,11,10,4,5,6,7,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,8,9,10,11,5,4,7,6,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1646Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1646Generator0 else (if j.val < 2 then node1646Generator1 else node1646Generator2))

def node1647Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,10,11,8,9,6,7,4,5,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,10,11,8,9,6,7,4,5,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1647Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,3,2,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1647Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,15,14,13,12,1,0,2,3,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,0,1,3,2,14,15,13,12,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1647Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1647Generator0 else (if j.val < 2 then node1647Generator1 else node1647Generator2))

def node1695Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1695Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1695Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1695Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,2,3,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1695Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,7,6,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,9,8,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1695Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1695Generator0 else node1695Generator1) else (if j.val < 3 then node1695Generator2 else (if j.val < 4 then node1695Generator3 else node1695Generator4)))

def node1696Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1696Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,4,5,2,3,8,9,6,7,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,4,5,2,3,8,9,6,7,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1696Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,5,4,2,3,6,7,8,9,12,13,10,11,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,4,5,3,2,6,7,8,9,12,13,10,11,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1696Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,10,11,12,13,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,10,11,12,13,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1696Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1696Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,6,7,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,8,9,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1696Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node1696Generator0 else (if j.val < 2 then node1696Generator1 else node1696Generator2)) else (if j.val < 4 then node1696Generator3 else (if j.val < 5 then node1696Generator4 else node1696Generator5)))

def node1697Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,10,11,4,5,6,7,9,8,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,10,11,4,5,6,7,9,8,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1697Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1697Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,6,7,8,9,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,12,13,6,7,8,9,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1697Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1697Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,7,6,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,9,8,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1697Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1697Generator0 else node1697Generator1) else (if j.val < 3 then node1697Generator2 else (if j.val < 4 then node1697Generator3 else node1697Generator4)))

def node1698Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,9,8,15,14,12,13,10,11,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,1,0,15,14,12,13,3,2,8,9,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1698Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,10,11,12,13,14,15,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,0,1,2,3,4,5,6,7,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1698Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,2,3,1,0,15,14,4,5,10,11,9,8,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,8,9,14,15,13,12,10,11,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1698Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1698Generator0 else (if j.val < 2 then node1698Generator1 else node1698Generator2))

def node1699Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,3,2,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,7,6,1,0,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1699Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,9,8,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1699Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,13,12,6,7,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,8,9,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1699Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1699Generator0 else (if j.val < 2 then node1699Generator1 else node1699Generator2))

def node1700Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1700Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1700Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1700Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1700Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1700Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1700Generator0 else node1700Generator1) else (if j.val < 3 then node1700Generator2 else (if j.val < 4 then node1700Generator3 else node1700Generator4)))

def node1701Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,11,10,13,12,6,7,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,10,11,12,13,7,6,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1701Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1701Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,15,14,4,5,9,8,11,10,13,12,6,7,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,15,14,4,5,12,13,7,6,9,8,11,10,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1701Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1701Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,5,4,2,3,11,10,13,12,7,6,8,9,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,3,2,11,10,12,13,7,6,9,8,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1701Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1701Generator0 else node1701Generator1) else (if j.val < 3 then node1701Generator2 else (if j.val < 4 then node1701Generator3 else node1701Generator4)))

def node1702Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,8,9,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1702Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,0,1,13,12,10,11,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,4,5,12,13,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1702Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,8,9,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,9,8,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1702Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1702Generator0 else (if j.val < 2 then node1702Generator1 else node1702Generator2))

def node1703Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,8,9,2,3,13,12,7,6,1,0,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,1,0,11,10,4,5,15,14,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1703Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,9,8,14,15,13,12,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,3,2,0,1,7,6,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1703Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,13,12,11,10,8,9,15,14,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,14,15,5,4,10,11,9,8,7,6,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1703Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1703Generator0 else (if j.val < 2 then node1703Generator1 else node1703Generator2))

def node1704Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,1,0,14,15,13,12,3,2,9,8,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,9,8,14,15,12,13,11,10,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1704Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,4,5,6,7,1,0,3,2,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,4,5,6,7,1,0,2,3,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1704Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,4,5,6,7,1,0,2,3,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,6,7,8,9,2,3,5,4,15,14,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1704Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1704Generator0 else (if j.val < 2 then node1704Generator1 else node1704Generator2))

def node1705Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,10,11,12,13,14,15,8,9,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,11,10,13,12,15,14,8,9,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1705Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1705Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,2,3,9,8,14,15,4,5,10,11,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,10,11,0,1,7,6,12,13,2,3,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1705Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1705Generator0 else (if j.val < 2 then node1705Generator1 else node1705Generator2))

def node1706Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,13,12,10,11,5,4,3,2,0,1,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,1,0,15,14,4,5,3,2,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1706Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,7,6,4,5,15,14,1,0,3,2,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,6,7,5,4,15,14,0,1,2,3,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1706Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,6,7,3,2,0,1,15,14,5,4,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,7,6,13,12,4,5,15,14,1,0,3,2,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1706Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1706Generator0 else (if j.val < 2 then node1706Generator1 else node1706Generator2))

def node1707Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1707Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,8,9,10,11,12,13,14,15,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,3,2,5,4,6,7,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1707Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,13,12,6,7,0,1,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,6,7,0,1,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1707Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,5,4,2,3,0,1,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,7,6,5,4,2,3,1,0,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1707Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1707Generator0 else node1707Generator1) else (if j.val < 3 then node1707Generator2 else node1707Generator3))

def node1708Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1708Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1708Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1708Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1708Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1708Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1708Generator0 else node1708Generator1) else (if j.val < 3 then node1708Generator2 else (if j.val < 4 then node1708Generator3 else node1708Generator4)))

def node1709Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1709Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,13,12,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1709Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,3,2,11,10,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,2,3,10,11,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1709Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1709Generator0 else (if j.val < 2 then node1709Generator1 else node1709Generator2))

def node1710Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,13,12,14,15,8,9,11,10,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,12,13,15,14,8,9,11,10,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1710Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,8,9,11,10,12,13,15,14,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,4,5,6,7,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1710Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,11,10,1,0,6,7,12,13,3,2,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,11,10,1,0,6,7,13,12,3,2,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1710Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,4,5,14,15,1,0,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,2,3,4,5,14,15,0,1,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1710Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,6,7,1,0,2,3,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,5,4,6,7,1,0,3,2,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1710Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1710Generator0 else node1710Generator1) else (if j.val < 3 then node1710Generator2 else (if j.val < 4 then node1710Generator3 else node1710Generator4)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
