import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1056 through 1087. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1245Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1245Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1245Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1245Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,3,2,5,4,14,15,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,7,6,0,1,11,10,13,12,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1245Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1245Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1245Generator0 else node1245Generator1) else (if j.val < 3 then node1245Generator2 else (if j.val < 4 then node1245Generator3 else node1245Generator4)))

def node1246Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1246Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1246Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1246Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,3,2,5,4,14,15,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,7,6,0,1,11,10,13,12,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1246Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1246Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1246Generator0 else node1246Generator1) else (if j.val < 3 then node1246Generator2 else (if j.val < 4 then node1246Generator3 else node1246Generator4)))

def node1247Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,15,14,12,13,10,11,9,8,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,15,14,12,13,11,10,8,9,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1247Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,8,9,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,11,10,6,7,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1247Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1247Generator0 else node1247Generator1)

def node1248Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1248Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,0,1,8,9,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,0,1,8,9,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1248Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1248Generator0 else node1248Generator1)

def node1249Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,15,14,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1249Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,8,9,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,11,10,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1249Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1249Generator0 else node1249Generator1)

def node1250Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1250Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,4,5,13,12,10,11,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,4,5,12,13,10,11,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1250Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1250Generator0 else node1250Generator1)

def node1251Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,0,1,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,0,1,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1251Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,10,11,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,13,12,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1251Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1251Generator0 else node1251Generator1)

def node1252Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,0,1,3,2,14,15,12,13,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,13,12,14,15,3,2,0,1,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1252Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,6,7,4,5,11,10,8,9,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,6,7,4,5,10,11,9,8,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1252Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,6,7,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,6,7,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1252Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1252Generator0 else (if j.val < 2 then node1252Generator1 else node1252Generator2))

def node1253Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,9,8,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1253Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,9,8,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1253Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,0,1,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,1,0,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1253Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1253Generator0 else (if j.val < 2 then node1253Generator1 else node1253Generator2))

def node1254Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,1,0,6,7,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,0,1,6,7,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1254Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,14,15,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1254Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,8,9,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1254Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1254Generator0 else (if j.val < 2 then node1254Generator1 else node1254Generator2))

def node1255Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,15,14,12,13,3,2,1,0,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,0,1,2,3,13,12,15,14,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1255Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,6,7,4,5,8,9,10,11,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,6,7,4,5,8,9,10,11,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1255Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1255Generator0 else node1255Generator1)

def node1256Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,10,11,9,8,4,5,7,6,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,8,9,11,10,7,6,4,5,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1256Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,15,14,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1256Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,14,15,13,12,0,1,3,2,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,3,2,0,1,14,15,13,12,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1256Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1256Generator0 else (if j.val < 2 then node1256Generator1 else node1256Generator2))

def node1257Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,0,1,2,3,13,12,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,12,13,14,15,3,2,0,1,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1257Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,15,14,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,13,12,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1257Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1257Generator0 else node1257Generator1)

def node1258Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,1,0,15,14,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,2,3,12,13,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1258Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,13,12,14,15,2,3,0,1,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,3,2,0,1,15,14,13,12,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1258Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1258Generator0 else node1258Generator1)

def node1259Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,6,7,5,4,10,11,9,8,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,7,6,4,5,11,10,8,9,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1259Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,10,11,9,8,4,5,6,7,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,8,9,10,11,7,6,4,5,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1259Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,3,2,1,0,12,13,14,15,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,13,12,14,15,0,1,2,3,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1259Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1259Generator0 else (if j.val < 2 then node1259Generator1 else node1259Generator2))

def node1260Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,3,2,15,14,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,3,2,14,15,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1260Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,4,5,7,6,9,8,11,10,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,4,5,7,6,9,8,11,10,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1260Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1260Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1260Generator0 else (if j.val < 2 then node1260Generator1 else node1260Generator2))

def node1261Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,8,9,11,10,6,7,4,5,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,10,11,8,9,4,5,7,6,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1261Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1261Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,6,7,4,5,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,6,7,4,5,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1261Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1261Generator0 else (if j.val < 2 then node1261Generator1 else node1261Generator2))

def node1262Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,13,12,15,14,1,0,2,3,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,1,0,3,2,12,13,15,14,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1262Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,6,7,4,5,10,11,8,9,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,6,7,4,5,10,11,8,9,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1262Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,9,8,10,11,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,11,10,5,4,6,7,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1262Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1262Generator0 else (if j.val < 2 then node1262Generator1 else node1262Generator2))

def node1263Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,15,14,7,6,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,9,8,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1263Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,7,6,8,9,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,7,6,8,9,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1263Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1263Generator0 else node1263Generator1)

def node1264Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1264Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,10,11,8,9,5,4,7,6,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,9,8,11,10,6,7,4,5,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1264Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1264Generator0 else node1264Generator1)

def node1265Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,11,10,9,8,6,7,4,5,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,10,11,8,9,7,6,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1265Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,6,7,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1265Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,14,15,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,13,12,15,14,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1265Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1265Generator0 else (if j.val < 2 then node1265Generator1 else node1265Generator2))

def node1266Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,2,3,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,13,12,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1266Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1266Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,11,10,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1266Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1266Generator0 else (if j.val < 2 then node1266Generator1 else node1266Generator2))

def node1267Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1267Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1267Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,5,4,15,14,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,7,6,0,1,11,10,13,12,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1267Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1267Generator0 else (if j.val < 2 then node1267Generator1 else node1267Generator2))

def node1268Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,14,15,13,12,10,11,8,9,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,15,14,12,13,10,11,8,9,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1268Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,8,9,10,11,14,15,13,12,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,1,0,2,3,4,5,6,7,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1268Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,8,9,10,11,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,8,9,10,11,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1268Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1268Generator0 else (if j.val < 2 then node1268Generator1 else node1268Generator2))

def node1269Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1269Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,6,7,11,10,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,6,7,10,11,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1269Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1269Generator0 else node1269Generator1)

def node1270Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,13,12,2,3,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,13,12,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1270Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,15,14,13,12,0,1,2,3,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,3,2,0,1,13,12,14,15,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1270Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1270Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1270Generator0 else (if j.val < 2 then node1270Generator1 else node1270Generator2))

def node1271Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,7,6,5,4,10,11,9,8,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,7,6,5,4,11,10,8,9,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1271Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,0,1,2,3,14,15,13,12,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,13,12,14,15,2,3,1,0,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1271Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1271Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1271Generator0 else (if j.val < 2 then node1271Generator1 else node1271Generator2))

def node1272Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1272Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,4,5,2,3,14,15,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,4,5,2,3,14,15,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1272Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1272Generator0 else node1272Generator1)

def node1273Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,2,3,0,1,4,5,6,7,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,8,9,10,11,13,12,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1273Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1273Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,14,15,13,12,10,11,9,8,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,15,14,12,13,11,10,8,9,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1273Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1273Generator0 else (if j.val < 2 then node1273Generator1 else node1273Generator2))

def node1274Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1274Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,12,13,15,14,3,2,0,1,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,2,3,1,0,15,14,13,12,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1274Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1274Generator0 else node1274Generator1)

def node1275Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,10,11,8,9,7,6,5,4,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,11,10,9,8,6,7,4,5,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1275Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,1,0,2,3,15,14,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,1,0,13,12,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1275Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,15,14,13,12,0,1,2,3,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,0,1,3,2,15,14,12,13,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1275Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1275Generator0 else (if j.val < 2 then node1275Generator1 else node1275Generator2))

def node1276Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,2,3,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1276Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,13,12,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1276Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,5,4,7,6,11,10,9,8,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,5,4,7,6,11,10,9,8,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1276Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1276Generator0 else (if j.val < 2 then node1276Generator1 else node1276Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
