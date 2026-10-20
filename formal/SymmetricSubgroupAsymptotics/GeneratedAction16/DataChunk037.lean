import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1184 through 1215. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1417Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1417Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1417Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1417Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1417Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,6,7,4,5,2,3,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,4,5,3,2,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1417Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1417Generator0 else node1417Generator1) else (if j.val < 3 then node1417Generator2 else (if j.val < 4 then node1417Generator3 else node1417Generator4)))

def node1418Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1418Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,15,14,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,14,15,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1418Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1418Generator0 else node1418Generator1)

def node1419Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,10,11,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1419Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,11,10,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1419Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1419Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1419Generator0 else (if j.val < 2 then node1419Generator1 else node1419Generator2))

def node1420Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1420Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,14,15,9,8,11,10,13,12,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,3,2,12,13,7,6,9,8,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1420Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,12,13,7,6,1,0,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,3,2,13,12,7,6,1,0,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1420Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1420Generator0 else (if j.val < 2 then node1420Generator1 else node1420Generator2))

def node1421Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,7,6,4,5,8,9,11,10,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,6,7,5,4,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1421Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,2,3,0,1,13,12,15,14,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,13,12,14,15,3,2,0,1,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1421Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1421Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1421Generator0 else (if j.val < 2 then node1421Generator1 else node1421Generator2))

def node1422Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,4,5,7,6,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,4,5,7,6,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1422Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,0,1,3,2,4,5,6,7,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,8,9,10,11,12,13,15,14,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1422Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1422Generator0 else node1422Generator1)

def node1423Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,9,8,11,10,15,14,12,13,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,3,2,0,1,5,4,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1423Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,10,11,8,9,12,13,15,14,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,2,3,1,0,6,7,4,5,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1423Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,10,11,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1423Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1423Generator0 else (if j.val < 2 then node1423Generator1 else node1423Generator2))

def node1424Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,1,0,15,14,5,4,3,2,9,8,6,7,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,9,8,7,6,12,13,11,10,1,0,14,15,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1424Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,4,5,15,14,9,8,2,3,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,10,11,4,5,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1424Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,1,0,10,11,5,4,14,15,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,9,8,2,3,13,12,6,7,1,0,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1424Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1424Generator0 else (if j.val < 2 then node1424Generator1 else node1424Generator2))

def node1425Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,8,9,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,6,7,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1425Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1425Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,12,13,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,12,13,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1425Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1425Generator0 else (if j.val < 2 then node1425Generator1 else node1425Generator2))

def node1426Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,1,0,12,13,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,0,1,15,14,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1426Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,15,14,13,12,3,2,0,1,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,2,3,0,1,15,14,12,13,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1426Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,15,14,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,13,12,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1426Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1426Generator0 else (if j.val < 2 then node1426Generator1 else node1426Generator2))

def node1427Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,13,12,6,7,1,0,11,10,4,5,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,10,11,4,5,15,14,9,8,3,2,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1427Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,4,5,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,11,10,4,5,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1427Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1427Generator0 else node1427Generator1)

def node1428Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,13,12,6,7,1,0,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,2,3,13,12,6,7,0,1,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1428Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,3,2,12,13,6,7,1,0,10,11,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,5,4,15,14,8,9,3,2,12,13,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1428Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1428Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1428Generator0 else (if j.val < 2 then node1428Generator1 else node1428Generator2))

def node1429Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1429Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,13,12,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,13,12,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1429Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,0,1,3,2,4,5,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,6,7,1,0,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1429Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1429Generator0 else (if j.val < 2 then node1429Generator1 else node1429Generator2))

def node1430Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,0,1,2,3,4,5,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,10,11,12,13,14,15,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1430Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,0,1,2,3,4,5,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,11,10,14,15,13,12,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1430Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,5,4,6,7,0,1,3,2,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,5,4,6,7,2,3,0,1,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1430Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1430Generator0 else (if j.val < 2 then node1430Generator1 else node1430Generator2))

def node1431Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,5,4,11,10,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,4,5,14,15,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1431Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,5,4,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,5,4,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1431Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,8,9,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1431Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1431Generator0 else (if j.val < 2 then node1431Generator1 else node1431Generator2))

def node1432Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,5,4,7,6,1,0,2,3,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,5,4,7,6,1,0,2,3,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1432Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,6,7,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,8,9,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1432Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1432Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1432Generator0 else (if j.val < 2 then node1432Generator1 else node1432Generator2))

def node1433Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,1,0,15,14,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,3,2,14,15,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1433Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1433Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,11,10,9,8,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,5,4,6,7,11,10,9,8,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1433Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1433Generator0 else (if j.val < 2 then node1433Generator1 else node1433Generator2))

def node1434Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,14,15,13,12,11,10,8,9,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,12,13,14,15,10,11,9,8,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1434Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,1,0,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,3,2,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1434Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,3,2,0,1,7,6,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,11,10,9,8,14,15,13,12,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1434Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1434Generator0 else (if j.val < 2 then node1434Generator1 else node1434Generator2))

def node1435Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,14,15,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1435Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,1,0,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1435Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,13,12,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1435Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1435Generator0 else (if j.val < 2 then node1435Generator1 else node1435Generator2))

def node1436Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1436Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,8,9,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,10,11,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1436Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1436Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1436Generator0 else (if j.val < 2 then node1436Generator1 else node1436Generator2))

def node1437Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,1,0,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,3,2,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1437Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1437Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1437Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1437Generator0 else (if j.val < 2 then node1437Generator1 else node1437Generator2))

def node1438Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1438Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,11,10,6,7,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,11,10,8,9,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1438Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,15,14,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,15,14,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1438Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1438Generator0 else (if j.val < 2 then node1438Generator1 else node1438Generator2))

def node1439Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1439Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1439Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1439Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1439Generator0 else (if j.val < 2 then node1439Generator1 else node1439Generator2))

def node1440Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,13,12,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1440Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,4,5,6,7,8,9,11,10,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,4,5,6,7,8,9,11,10,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1440Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1440Generator0 else node1440Generator1)

def node1441Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,15,14,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1441Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,12,13,14,15,0,1,3,2,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,2,3,0,1,15,14,13,12,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1441Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1441Generator0 else node1441Generator1)

def node1442Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,14,15,12,13,10,11,8,9,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,12,13,15,14,10,11,8,9,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1442Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,3,2,14,15,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,3,2,14,15,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1442Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,4,5,6,7,1,0,2,3,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,4,5,6,7,0,1,3,2,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1442Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1442Generator0 else (if j.val < 2 then node1442Generator1 else node1442Generator2))

def node1443Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1443Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,15,14,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,15,14,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1443Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,6,7,4,5,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,10,11,8,9,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1443Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1443Generator0 else (if j.val < 2 then node1443Generator1 else node1443Generator2))

def node1444Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,5,4,7,6,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,7,6,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1444Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,3,2,1,0,14,15,12,13,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,12,13,14,15,1,0,2,3,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1444Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1444Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1444Generator0 else (if j.val < 2 then node1444Generator1 else node1444Generator2))

def node1445Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1445Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,4,5,7,6,3,2,0,1,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,7,6,0,1,3,2,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1445Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,11,10,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,9,8,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1445Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1445Generator0 else (if j.val < 2 then node1445Generator1 else node1445Generator2))

def node1446Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,13,12,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1446Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,15,14,12,13,0,1,3,2,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,2,3,0,1,13,12,14,15,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1446Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,9,8,10,11,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,11,10,9,8,5,4,6,7,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1446Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1446Generator0 else (if j.val < 2 then node1446Generator1 else node1446Generator2))

def node1447Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,7,6,4,5,9,8,10,11,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,6,7,5,4,9,8,10,11,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1447Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,1,0,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1447Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1447Generator0 else node1447Generator1)

def node1448Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,9,8,10,11,5,4,6,7,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,9,8,10,11,5,4,6,7,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1448Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,1,0,3,2,12,13,14,15,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,13,12,15,14,3,2,1,0,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1448Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1448Generator0 else node1448Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
