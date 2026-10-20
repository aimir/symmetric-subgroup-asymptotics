import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1216 through 1247. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1449Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1449Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,4,5,3,2,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,7,6,4,5,3,2,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1449Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,2,3,9,8,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,2,3,9,8,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1449Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1449Generator0 else (if j.val < 2 then node1449Generator1 else node1449Generator2))

def node1450Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,12,13,14,15,1,0,3,2,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,1,0,2,3,12,13,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1450Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,14,15,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1450Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,0,1,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,2,3,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1450Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1450Generator0 else (if j.val < 2 then node1450Generator1 else node1450Generator2))

def node1451Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,9,8,10,11,4,5,7,6,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,11,10,5,4,6,7,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1451Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1451Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,15,14,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1451Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1451Generator0 else (if j.val < 2 then node1451Generator1 else node1451Generator2))

def node1452Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1452Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,8,9,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,11,10,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1452Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1452Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1452Generator0 else (if j.val < 2 then node1452Generator1 else node1452Generator2))

def node1453Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,11,10,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,11,10,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1453Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1453Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1453Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1453Generator0 else (if j.val < 2 then node1453Generator1 else node1453Generator2))

def node1454Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1454Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,6,7,5,4,0,1,2,3,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,7,6,4,5,1,0,3,2,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1454Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,10,11,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,8,9,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1454Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1454Generator0 else (if j.val < 2 then node1454Generator1 else node1454Generator2))

def node1455Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,11,10,9,8,14,15,13,12,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,1,0,2,3,7,6,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1455Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,4,5,7,6,2,3,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,4,5,7,6,3,2,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1455Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,6,7,11,10,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,6,7,10,11,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1455Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1455Generator0 else (if j.val < 2 then node1455Generator1 else node1455Generator2))

def node1456Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,2,3,1,0,7,6,5,4,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,11,10,9,8,12,13,14,15,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1456Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,15,14,13,12,10,11,9,8,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,15,14,13,12,11,10,8,9,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1456Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,9,8,10,11,15,14,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,0,1,3,2,5,4,6,7,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1456Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1456Generator0 else (if j.val < 2 then node1456Generator1 else node1456Generator2))

def node1457Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1457Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1457Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,11,10,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,8,9,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1457Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1457Generator0 else (if j.val < 2 then node1457Generator1 else node1457Generator2))

def node1458Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,15,14,13,12,10,11,9,8,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,14,15,12,13,11,10,8,9,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1458Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,3,2,15,14,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,2,3,0,1,14,15,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1458Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,12,13,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,13,12,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1458Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1458Generator0 else (if j.val < 2 then node1458Generator1 else node1458Generator2))

def node1459Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,11,10,8,9,4,5,7,6,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,8,9,11,10,6,7,5,4,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1459Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,0,1,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,12,13,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1459Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,13,12,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,15,14,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1459Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1459Generator0 else (if j.val < 2 then node1459Generator1 else node1459Generator2))

def node1460Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,4,5,6,7,10,11,9,8,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,4,5,6,7,11,10,8,9,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1460Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1460Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1460Generator0 else node1460Generator1)

def node1461Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,14,15,1,0,11,10,12,13,6,7,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,10,11,13,12,7,6,8,9,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1461Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,13,12,10,11,0,1,15,14,5,4,2,3,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,12,13,11,10,0,1,15,14,4,5,3,2,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1461Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,15,14,9,8,10,11,12,13,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,13,12,7,6,8,9,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1461Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1461Generator0 else (if j.val < 2 then node1461Generator1 else node1461Generator2))

def node1462Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,1,0,3,2,5,4,7,6,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,9,8,11,10,13,12,15,14,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1462Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,8,9,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,9,8,6,7,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1462Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,7,6,4,5,2,3,1,0,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,7,6,5,4,3,2,0,1,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1462Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1462Generator0 else (if j.val < 2 then node1462Generator1 else node1462Generator2))

def node1463Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,0,1,14,15,5,4,2,3,9,8,6,7,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,8,9,7,6,12,13,11,10,1,0,14,15,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1463Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,8,9,11,10,13,12,15,14,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,2,3,4,5,7,6,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1463Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,14,15,12,13,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1463Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1463Generator0 else (if j.val < 2 then node1463Generator1 else node1463Generator2))

def node1464Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,1,0,2,3,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,3,2,1,0,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1464Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,15,14,12,13,1,0,2,3,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,0,1,2,3,15,14,12,13,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1464Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,8,9,10,11,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,10,11,9,8,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1464Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1464Generator0 else (if j.val < 2 then node1464Generator1 else node1464Generator2))

def node1465Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,9,8,11,10,13,12,14,15,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,1,0,3,2,5,4,7,6,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1465Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,6,7,5,4,3,2,0,1,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,6,7,4,5,2,3,1,0,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1465Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1465Generator0 else node1465Generator1)

def node1466Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,3,2,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,3,2,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1466Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,7,6,3,2,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,5,4,7,6,1,0,3,2,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1466Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1466Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1466Generator0 else (if j.val < 2 then node1466Generator1 else node1466Generator2))

def node1467Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,5,4,6,7,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1467Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,10,11,9,8,15,14,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,3,2,7,6,4,5,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1467Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1467Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1467Generator0 else (if j.val < 2 then node1467Generator1 else node1467Generator2))

def node1468Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,13,12,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,1,0,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1468Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,9,8,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1468Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1468Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1468Generator0 else (if j.val < 2 then node1468Generator1 else node1468Generator2))

def node1469Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,0,1,2,3,4,5,6,7,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,8,9,10,11,12,13,15,14,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1469Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,4,5,11,10,1,0,6,7,12,13,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,4,5,10,11,1,0,7,6,12,13,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1469Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1469Generator0 else node1469Generator1)

def node1470Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,11,10,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1470Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,11,10,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1470Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,14,15,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,12,13,14,15,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1470Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1470Generator0 else (if j.val < 2 then node1470Generator1 else node1470Generator2))

def node1471Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,9,8,11,10,5,4,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,10,11,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1471Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,1,0,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,13,12,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1471Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,14,15,9,8,10,11,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,15,14,13,12,9,8,10,11,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1471Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1471Generator0 else (if j.val < 2 then node1471Generator1 else node1471Generator2))

def node1472Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,15,14,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,15,14,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1472Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,11,10,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,9,8,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1472Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1472Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1472Generator0 else (if j.val < 2 then node1472Generator1 else node1472Generator2))

def node1473Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,10,11,8,9,13,12,15,14,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,1,0,2,3,6,7,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1473Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,10,11,5,4,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,11,10,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1473Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,4,5,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,5,4,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1473Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1473Generator0 else (if j.val < 2 then node1473Generator1 else node1473Generator2))

def node1474Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1474Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,8,9,11,10,5,4,6,7,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,9,8,10,11,4,5,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1474Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1474Generator0 else node1474Generator1)

def node1475Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,7,6,0,1,2,3,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,5,4,7,6,1,0,3,2,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1475Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,5,4,7,6,2,3,1,0,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,5,4,7,6,1,0,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1475Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,3,2,0,1,7,6,4,5,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,10,11,9,8,12,13,15,14,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1475Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1475Generator0 else (if j.val < 2 then node1475Generator1 else node1475Generator2))

def node1476Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,13,12,14,15,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1476Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,6,7,4,5,9,8,10,11,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,6,7,4,5,9,8,10,11,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1476Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1476Generator0 else node1476Generator1)

def node1477Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1477Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,4,5,7,6,1,0,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,4,5,7,6,2,3,0,1,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1477Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,11,10,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,8,9,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1477Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1477Generator0 else (if j.val < 2 then node1477Generator1 else node1477Generator2))

def node1478Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,14,15,10,11,8,9,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,12,13,15,14,10,11,8,9,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1478Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,7,6,5,4,1,0,2,3,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,7,6,5,4,3,2,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1478Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,9,8,11,10,12,13,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,3,2,0,1,5,4,7,6,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1478Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1478Generator0 else (if j.val < 2 then node1478Generator1 else node1478Generator2))

def node1479Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,10,11,8,9,15,14,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,3,2,0,1,6,7,4,5,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1479Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,1,0,15,14,4,5,2,3,9,8,6,7,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,8,9,6,7,12,13,11,10,1,0,14,15,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1479Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,9,8,6,7,13,12,10,11,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,8,9,7,6,12,13,11,10,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1479Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1479Generator0 else (if j.val < 2 then node1479Generator1 else node1479Generator2))

def node1480Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,12,13,15,14,11,10,9,8,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,12,13,15,14,11,10,9,8,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1480Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,6,7,5,4,2,3,1,0,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,7,6,4,5,3,2,0,1,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1480Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,9,8,11,10,15,14,12,13,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,1,0,3,2,5,4,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1480Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1480Generator0 else (if j.val < 2 then node1480Generator1 else node1480Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
