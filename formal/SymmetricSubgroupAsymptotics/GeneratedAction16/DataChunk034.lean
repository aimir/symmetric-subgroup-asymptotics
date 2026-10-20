import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1088 through 1119. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1277Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,11,10,9,8,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,3,2,0,1,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1277Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,3,2,1,0,4,5,7,6,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,8,9,11,10,15,14,12,13,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1277Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1277Generator0 else node1277Generator1)

def node1278Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,3,2,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,2,3,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1278Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,11,10,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1278Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1278Generator0 else node1278Generator1)

def node1279Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,15,14,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,13,12,14,15,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1279Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,1,0,2,3,12,13,15,14,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,14,15,13,12,3,2,1,0,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1279Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1279Generator0 else node1279Generator1)

def node1280Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,2,3,0,1,15,14,12,13,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,14,15,12,13,1,0,3,2,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1280Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,14,15,13,12,1,0,2,3,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,2,3,1,0,13,12,14,15,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1280Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,10,11,9,8,4,5,6,7,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,8,9,10,11,7,6,4,5,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1280Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1280Generator0 else (if j.val < 2 then node1280Generator1 else node1280Generator2))

def node1281Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,8,9,11,10,13,12,15,14,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,1,0,3,2,4,5,7,6,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1281Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,3,2,0,1,5,4,7,6,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,9,8,11,10,12,13,15,14,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1281Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1281Generator0 else node1281Generator1)

def node1282Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1282Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1282Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,6,7,4,5,1,0,2,3,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,6,7,4,5,1,0,2,3,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1282Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,15,14,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1282Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1282Generator0 else node1282Generator1) else (if j.val < 3 then node1282Generator2 else node1282Generator3))

def node1283Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,13,12,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1283Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,5,4,7,6,11,10,8,9,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,5,4,7,6,10,11,9,8,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1283Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1283Generator0 else node1283Generator1)

def node1284Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,5,4,7,6,11,10,8,9,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,5,4,7,6,10,11,9,8,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1284Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1284Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1284Generator0 else node1284Generator1)

def node1285Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,11,10,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,9,8,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1285Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,7,6,4,5,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,6,7,5,4,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1285Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,10,11,8,9,15,14,12,13,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,0,1,3,2,6,7,4,5,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1285Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1285Generator0 else (if j.val < 2 then node1285Generator1 else node1285Generator2))

def node1330Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1330Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,5,4,3,2,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,5,4,3,2,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1330Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1330Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1330Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,9,8,10,11,14,15,5,4,3,2,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,11,10,9,8,12,13,3,2,4,5,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1330Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1330Generator0 else node1330Generator1) else (if j.val < 3 then node1330Generator2 else (if j.val < 4 then node1330Generator3 else node1330Generator4)))

def node1331Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1331Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,5,4,3,2,6,7,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,5,4,3,2,6,7,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1331Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1331Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1331Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,9,8,10,11,14,15,5,4,3,2,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,11,10,9,8,12,13,3,2,4,5,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1331Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1331Generator0 else node1331Generator1) else (if j.val < 3 then node1331Generator2 else (if j.val < 4 then node1331Generator3 else node1331Generator4)))

def node1332Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1332Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1332Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1332Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1332Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1332Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1332Generator0 else node1332Generator1) else (if j.val < 3 then node1332Generator2 else (if j.val < 4 then node1332Generator3 else node1332Generator4)))

def node1333Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1333Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1333Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,3,2,4,5,1,0,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,3,2,4,5,0,1,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1333Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1333Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,14,15,13,12,9,8,1,0,6,7,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,12,13,14,15,10,11,7,6,1,0,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1333Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1333Generator0 else node1333Generator1) else (if j.val < 3 then node1333Generator2 else (if j.val < 4 then node1333Generator3 else node1333Generator4)))

def node1334Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1334Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,5,4,3,2,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,5,4,3,2,6,7,10,11,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1334Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1334Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1334Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,9,8,10,11,14,15,5,4,3,2,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,11,10,9,8,12,13,3,2,4,5,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1334Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1334Generator0 else node1334Generator1) else (if j.val < 3 then node1334Generator2 else (if j.val < 4 then node1334Generator3 else node1334Generator4)))

def node1335Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1335Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1335Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,9,8,10,11,12,13,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,0,1,3,2,5,4,6,7,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1335Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,11,10,9,8,15,14,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,3,2,0,1,7,6,5,4,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1335Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,12,13,7,6,1,0,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,3,2,13,12,7,6,1,0,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1335Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1335Generator0 else node1335Generator1) else (if j.val < 3 then node1335Generator2 else (if j.val < 4 then node1335Generator3 else node1335Generator4)))

def node1336Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,9,8,7,6,13,12,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,9,8,7,6,12,13,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1336Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1336Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1336Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1336Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,3,2,6,7,9,8,10,11,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,6,7,9,8,10,11,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1336Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1336Generator0 else node1336Generator1) else (if j.val < 3 then node1336Generator2 else (if j.val < 4 then node1336Generator3 else node1336Generator4)))

def node1337Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1337Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,9,8,10,11,4,5,7,6,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,11,10,5,4,6,7,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1337Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1337Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1337Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1337Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,14,15,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1337Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node1337Generator0 else (if j.val < 2 then node1337Generator1 else node1337Generator2)) else (if j.val < 4 then node1337Generator3 else (if j.val < 5 then node1337Generator4 else node1337Generator5)))

def node1338Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1338Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,11,10,8,9,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1338Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1338Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1338Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1338Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1338Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node1338Generator0 else (if j.val < 2 then node1338Generator1 else node1338Generator2)) else (if j.val < 4 then node1338Generator3 else (if j.val < 5 then node1338Generator4 else node1338Generator5)))

def node1339Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1339Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1339Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1339Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,3,2,4,5,1,0,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,3,2,4,5,1,0,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1339Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,14,15,13,12,9,8,1,0,6,7,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,12,13,14,15,10,11,7,6,1,0,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1339Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1339Generator0 else node1339Generator1) else (if j.val < 3 then node1339Generator2 else (if j.val < 4 then node1339Generator3 else node1339Generator4)))

def node1340Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1340Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1340Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1340Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1340Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,4,5,6,7,3,2,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,6,7,2,3,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1340Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1340Generator0 else node1340Generator1) else (if j.val < 3 then node1340Generator2 else (if j.val < 4 then node1340Generator3 else node1340Generator4)))

def node1341Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1341Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,6,7,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,6,7,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1341Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1341Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1341Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,9,8,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,10,11,7,6,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1341Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1341Generator0 else node1341Generator1) else (if j.val < 3 then node1341Generator2 else (if j.val < 4 then node1341Generator3 else node1341Generator4)))

def node1342Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1342Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1342Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1342Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1342Generator0 else (if j.val < 2 then node1342Generator1 else node1342Generator2))

def node1343Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,14,15,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1343Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,1,0,15,14,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,5,4,10,11,13,12,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1343Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,4,5,3,2,8,9,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,4,5,2,3,8,9,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1343Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1343Generator0 else (if j.val < 2 then node1343Generator1 else node1343Generator2))

def node1344Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,11,10,9,8,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,10,11,8,9,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1344Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,13,12,15,14,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,3,2,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1344Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,2,3,0,1,13,12,15,14,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,15,14,12,13,2,3,1,0,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1344Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1344Generator0 else (if j.val < 2 then node1344Generator1 else node1344Generator2))

def node1345Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,1,0,6,7,12,13,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,1,0,6,7,13,12,10,11,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1345Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,2,3,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,2,3,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1345Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,13,12,1,0,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,13,12,11,10,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1345Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1345Generator0 else (if j.val < 2 then node1345Generator1 else node1345Generator2))

def node1346Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,14,15,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,15,14,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1346Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1346Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,2,3,1,0,6,7,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,11,10,8,9,14,15,13,12,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1346Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1346Generator0 else (if j.val < 2 then node1346Generator1 else node1346Generator2))

def node1347Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1347Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,9,8,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,9,8,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1347Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1347Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1347Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,4,5,6,7,3,2,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,6,7,2,3,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1347Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1347Generator0 else node1347Generator1) else (if j.val < 3 then node1347Generator2 else (if j.val < 4 then node1347Generator3 else node1347Generator4)))

def node1348Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1348Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,6,7,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1348Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1348Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1348Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,4,5,6,7,2,3,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,4,5,6,7,3,2,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1348Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1348Generator0 else node1348Generator1) else (if j.val < 3 then node1348Generator2 else (if j.val < 4 then node1348Generator3 else node1348Generator4)))

def node1349Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1349Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1349Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1349Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1349Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1349Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1349Generator0 else node1349Generator1) else (if j.val < 3 then node1349Generator2 else (if j.val < 4 then node1349Generator3 else node1349Generator4)))

def node1350Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1350Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,7,6,5,4,11,10,9,8,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,7,6,5,4,11,10,9,8,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1350Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1350Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1350Generator0 else (if j.val < 2 then node1350Generator1 else node1350Generator2))

def node1351Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,1,0,3,2,5,4,6,7,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,9,8,11,10,12,13,14,15,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1351Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,9,8,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,9,8,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1351Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1351Generator0 else node1351Generator1)

def node1352Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1352Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1352Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1352Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1352Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1352Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1352Generator0 else node1352Generator1) else (if j.val < 3 then node1352Generator2 else (if j.val < 4 then node1352Generator3 else node1352Generator4)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
