import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1408 through 1426. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1743Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,1,0,9,8,15,14,12,13,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,3,2,5,4,9,8,14,15,12,13,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1743Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,13,12,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,15,14,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1743Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1743Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1743Generator0 else (if j.val < 2 then node1743Generator1 else node1743Generator2))

def node1744Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,1,0,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,0,1,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1744Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,2,3,4,5,9,8,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1,9,8,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1744Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,11,10,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1744Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1744Generator0 else (if j.val < 2 then node1744Generator1 else node1744Generator2))

def node1745Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,6,7,12,13,1,0,2,3,4,5,14,15,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,8,9,10,11,2,3,0,1,14,15,4,5,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1745Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,15,14,4,5,9,8,10,11,13,12,7,6,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,15,14,4,5,13,12,7,6,8,9,11,10,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1745Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,11,10,1,0,2,3,5,4,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,8,9,11,10,0,1,2,3,5,4,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1745Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1745Generator0 else (if j.val < 2 then node1745Generator1 else node1745Generator2))

def node1746Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,9,8,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1746Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,1,0,7,6,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,1,0,7,6,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1746Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,14,15,13,12,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,13,12,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1746Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1746Generator0 else (if j.val < 2 then node1746Generator1 else node1746Generator2))

def node1769Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1769Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,6,7,8,9,10,11,4,5,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,12,13,6,7,8,9,10,11,5,4,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1769Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,10,11,12,13,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,10,11,12,13,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1769Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,6,7,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,8,9,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1769Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1769Generator0 else node1769Generator1) else (if j.val < 3 then node1769Generator2 else node1769Generator3))

def node1770Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,0,1,3,2,4,5,7,6,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,9,8,10,11,13,12,14,15,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1770Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,10,11,1,0,15,14,12,13,2,3,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,12,13,2,3,1,0,15,14,4,5,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1770Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,7,6,0,1,3,2,5,4,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,9,8,3,2,13,12,15,14,0,1,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1770Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1770Generator0 else (if j.val < 2 then node1770Generator1 else node1770Generator2))

def node1771Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,14,15,8,9,10,11,12,13,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,1,0,11,10,4,5,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1771Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,12,13,15,14,1,0,10,11,4,5,7,6,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,1,0,10,11,13,12,14,15,8,9,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1771Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,8,9,11,10,12,13,15,14,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,1,0,2,3,5,4,6,7,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1771Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1771Generator0 else (if j.val < 2 then node1771Generator1 else node1771Generator2))

def node1772Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,10,11,4,5,6,7,9,8,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,10,11,4,5,6,7,9,8,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1772Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,6,7,8,9,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,12,13,6,7,8,9,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1772Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,8,9,10,11,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,2,3,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1772Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,11,10,1,0,6,7,12,13,3,2,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,11,10,1,0,6,7,13,12,3,2,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1772Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,2,3,5,4,6,7,1,0,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,2,3,5,4,6,7,1,0,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1772Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1772Generator0 else node1772Generator1) else (if j.val < 3 then node1772Generator2 else (if j.val < 4 then node1772Generator3 else node1772Generator4)))

def node1773Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,13,12,10,11,1,0,14,15,4,5,2,3,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,12,13,10,11,0,1,15,14,4,5,3,2,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1773Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,9,8,3,2,12,13,14,15,1,0,11,10,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,5,4,14,15,1,0,3,2,13,12,6,7,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1773Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,4,5,7,6,1,0,3,2,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,6,7,9,8,2,3,5,4,15,14,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1773Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1773Generator0 else (if j.val < 2 then node1773Generator1 else node1773Generator2))

def node1774Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,15,14,5,4,3,2,8,9,6,7,12,13,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,5,4,10,11,8,9,14,15,12,13,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1774Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,5,4,10,11,8,9,15,14,12,13,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,14,15,5,4,3,2,8,9,6,7,12,13,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1774Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,5,4,3,2,0,1,6,7,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,8,9,14,15,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1774Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1774Generator0 else (if j.val < 2 then node1774Generator1 else node1774Generator2))

def node1775Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1775Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,8,9,10,11,12,13,14,15,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,3,2,5,4,6,7,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1775Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,2,3,4,5,15,14,0,1,10,11,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,2,3,4,5,14,15,1,0,10,11,12,13,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1775Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,3,2,8,9,14,15,4,5,10,11,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,3,2,8,9,15,14,4,5,10,11,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1775Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1775Generator0 else node1775Generator1) else (if j.val < 3 then node1775Generator2 else node1775Generator3))

def node1776Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,5,4,7,6,0,1,2,3,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,5,4,7,6,0,1,2,3,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1776Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,4,5,2,3,0,1,7,6,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,13,12,3,2,0,1,15,14,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1776Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,13,12,15,14,8,9,10,11,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,10,11,12,13,6,7,8,9,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1776Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1776Generator0 else (if j.val < 2 then node1776Generator1 else node1776Generator2))

def node1777Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,3,2,1,0,7,6,5,4,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,11,10,9,8,15,14,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1777Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,5,4,2,3,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,5,4,3,2,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1777Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,12,13,14,15,9,8,11,10,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,11,10,13,12,7,6,9,8,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1777Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1777Generator0 else (if j.val < 2 then node1777Generator1 else node1777Generator2))

def node1778Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1778Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,8,9,10,11,12,13,6,7,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,12,13,6,7,8,9,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1778Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,1,0,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1778Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1778Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,6,7,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,8,9,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1778Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1778Generator0 else node1778Generator1) else (if j.val < 3 then node1778Generator2 else (if j.val < 4 then node1778Generator3 else node1778Generator4)))

def node1779Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,10,11,4,5,6,7,9,8,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,10,11,4,5,6,7,9,8,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1779Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,6,7,8,9,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,12,13,6,7,8,9,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1779Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,14,15,9,8,11,10,13,12,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,3,2,12,13,7,6,9,8,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1779Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,11,10,1,0,7,6,12,13,2,3,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,10,11,0,1,7,6,13,12,3,2,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1779Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,2,3,5,4,6,7,1,0,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,2,3,5,4,6,7,1,0,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1779Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1779Generator0 else node1779Generator1) else (if j.val < 3 then node1779Generator2 else (if j.val < 4 then node1779Generator3 else node1779Generator4)))

def node1780Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1780Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,14,15,9,8,11,10,13,12,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,3,2,12,13,7,6,9,8,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1780Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,11,10,1,0,6,7,12,13,3,2,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,11,10,1,0,6,7,13,12,3,2,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1780Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,2,3,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1780Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1780Generator0 else node1780Generator1) else (if j.val < 3 then node1780Generator2 else node1780Generator3))

def node1781Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,14,15,4,5,11,10,8,9,6,7,13,12,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,14,15,4,5,10,11,8,9,7,6,13,12,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1781Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,4,5,6,7,8,9,2,3,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,10,11,4,5,6,7,8,9,3,2,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1781Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,8,9,10,11,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,2,3,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1781Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,2,3,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1781Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1781Generator0 else node1781Generator1) else (if j.val < 3 then node1781Generator2 else node1781Generator3))

def node1782Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,15,14,5,4,10,11,9,8,6,7,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,12,13,11,10,8,9,15,14,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1782Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,4,5,2,3,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,5,4,2,3,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1782Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,0,1,10,11,5,4,7,6,9,8,3,2,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,13,12,7,6,9,8,11,10,4,5,14,15,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1782Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1782Generator0 else (if j.val < 2 then node1782Generator1 else node1782Generator2))

def node1823Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1823Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,6,7,8,9,10,11,4,5,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,12,13,6,7,8,9,10,11,5,4,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1823Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,8,9,10,11,12,13,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,12,13,6,7,8,9,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1823Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,1,0,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1823Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1823Generator0 else node1823Generator1) else (if j.val < 3 then node1823Generator2 else node1823Generator3))

end SymmetricSubgroupAsymptotics.BinaryActionData16
