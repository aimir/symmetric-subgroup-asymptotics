import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
960 through 991. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1149Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,11,10,8,9,12,13,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,2,3,1,0,6,7,5,4,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1149Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,14,15,12,13,10,11,8,9,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,15,14,13,12,10,11,8,9,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1149Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,13,12,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1149Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1149Generator0 else (if j.val < 2 then node1149Generator1 else node1149Generator2))

def node1150Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,11,10,9,8,13,12,15,14,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,2,3,0,1,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1150Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1150Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1150Generator0 else node1150Generator1)

def node1151Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1151Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1151Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1151Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1151Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1151Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1151Generator0 else node1151Generator1) else (if j.val < 3 then node1151Generator2 else (if j.val < 4 then node1151Generator3 else node1151Generator4)))

def node1152Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1152Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1152Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1152Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1152Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1152Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1152Generator0 else node1152Generator1) else (if j.val < 3 then node1152Generator2 else (if j.val < 4 then node1152Generator3 else node1152Generator4)))

def node1153Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1153Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,15,14,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1153Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1153Generator0 else node1153Generator1)

def node1154Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,0,1,14,15,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,1,0,15,14,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1154Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,10,11,8,9,12,13,14,15,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,3,2,1,0,6,7,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1154Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,3,2,0,1,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,3,2,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1154Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1154Generator0 else (if j.val < 2 then node1154Generator1 else node1154Generator2))

def node1155Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,9,8,10,11,12,13,14,15,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,1,0,3,2,5,4,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1155Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,11,10,8,9,13,12,15,14,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,2,3,0,1,6,7,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1155Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1155Generator0 else node1155Generator1)

def node1156Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,14,15,1,0,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,13,12,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1156Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,0,1,3,2,4,5,7,6,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,8,9,11,10,15,14,13,12,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1156Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1156Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1156Generator0 else (if j.val < 2 then node1156Generator1 else node1156Generator2))

def node1157Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1157Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,7,6,11,10,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,7,6,10,11,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1157Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,7,6,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,6,7,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1157Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,0,1,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,0,1,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1157Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1157Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1157Generator0 else node1157Generator1) else (if j.val < 3 then node1157Generator2 else (if j.val < 4 then node1157Generator3 else node1157Generator4)))

def node1158Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,8,9,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,15,14,6,7,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1158Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,11,10,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,12,13,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1158Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,4,5,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,4,5,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1158Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1158Generator0 else (if j.val < 2 then node1158Generator1 else node1158Generator2))

def node1159Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1159Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1159Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,7,6,11,10,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,7,6,10,11,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1159Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1159Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1159Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1159Generator0 else node1159Generator1) else (if j.val < 3 then node1159Generator2 else (if j.val < 4 then node1159Generator3 else node1159Generator4)))

def node1160Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,1,0,13,12,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,1,0,15,14,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1160Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,1,0,2,3,7,6,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,10,11,9,8,13,12,15,14,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1160Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,7,6,5,4,0,1,3,2,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,7,6,5,4,2,3,0,1,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1160Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1160Generator0 else (if j.val < 2 then node1160Generator1 else node1160Generator2))

def node1161Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,8,9,1,0,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,13,12,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1161Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,10,11,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,15,14,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1161Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,14,15,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1161Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1161Generator0 else (if j.val < 2 then node1161Generator1 else node1161Generator2))

def node1162Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,8,9,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1162Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,12,13,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1162Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1162Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1162Generator0 else (if j.val < 2 then node1162Generator1 else node1162Generator2))

def node1163Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1163Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1163Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1163Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1163Generator0 else (if j.val < 2 then node1163Generator1 else node1163Generator2))

def node1164Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,6,7,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1164Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,0,1,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,12,13,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1164Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1164Generator0 else node1164Generator1)

def node1165Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1165Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,15,14,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,8,9,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1165Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1165Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1165Generator0 else (if j.val < 2 then node1165Generator1 else node1165Generator2))

def node1166Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1166Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1166Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1166Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,2,3,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,1,0,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1166Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1166Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1166Generator0 else node1166Generator1) else (if j.val < 3 then node1166Generator2 else (if j.val < 4 then node1166Generator3 else node1166Generator4)))

def node1167Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1167Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1167Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,0,1,10,11,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,0,1,10,11,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1167Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1167Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,14,15,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1167Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1167Generator0 else node1167Generator1) else (if j.val < 3 then node1167Generator2 else (if j.val < 4 then node1167Generator3 else node1167Generator4)))

def node1168Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,8,9,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,10,11,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1168Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,1,0,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,2,3,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1168Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1168Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1168Generator0 else (if j.val < 2 then node1168Generator1 else node1168Generator2))

def node1169Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1169Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1169Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1169Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1169Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1169Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1169Generator0 else node1169Generator1) else (if j.val < 3 then node1169Generator2 else (if j.val < 4 then node1169Generator3 else node1169Generator4)))

def node1170Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,13,12,15,14,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1170Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1170Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,8,9,11,10,6,7,4,5,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,10,11,8,9,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1170Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1170Generator0 else (if j.val < 2 then node1170Generator1 else node1170Generator2))

def node1171Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1171Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1171Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,8,9,10,11,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,2,3,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1171Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,4,5,2,3,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,5,4,2,3,1,0,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1171Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1171Generator0 else node1171Generator1) else (if j.val < 3 then node1171Generator2 else node1171Generator3))

def node1172Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1172Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1172Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,0,1,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,2,3,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1172Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1172Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,6,7,4,5,2,3,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,4,5,3,2,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1172Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1172Generator0 else node1172Generator1) else (if j.val < 3 then node1172Generator2 else (if j.val < 4 then node1172Generator3 else node1172Generator4)))

def node1173Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,15,14,13,12,0,1,2,3,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,0,1,2,3,12,13,15,14,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1173Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,12,13,15,14,3,2,0,1,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,1,0,2,3,14,15,13,12,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1173Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,1,0,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,3,2,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1173Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1173Generator0 else (if j.val < 2 then node1173Generator1 else node1173Generator2))

def node1174Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,13,12,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1174Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,7,6,5,4,9,8,11,10,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,7,6,5,4,9,8,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1174Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,8,9,11,10,7,6,4,5,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,10,11,9,8,4,5,7,6,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1174Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1174Generator0 else (if j.val < 2 then node1174Generator1 else node1174Generator2))

def node1175Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1175Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1175Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,5,4,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,4,5,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1175Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1175Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1175Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1175Generator0 else node1175Generator1) else (if j.val < 3 then node1175Generator2 else (if j.val < 4 then node1175Generator3 else node1175Generator4)))

def node1176Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,1,0,2,3,6,7,4,5,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,10,11,8,9,14,15,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1176Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,12,13,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,12,13,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1176Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1176Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1176Generator0 else (if j.val < 2 then node1176Generator1 else node1176Generator2))

def node1177Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1177Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1177Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1177Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,15,14,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,12,13,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1177Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1177Generator0 else node1177Generator1) else (if j.val < 3 then node1177Generator2 else node1177Generator3))

def node1178Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,3,2,1,0,13,12,15,14,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,15,14,12,13,2,3,1,0,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1178Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,0,1,2,3,13,12,15,14,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,13,12,14,15,0,1,3,2,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1178Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,12,13,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,13,12,14,15,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1178Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1178Generator0 else (if j.val < 2 then node1178Generator1 else node1178Generator2))

def node1179Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1179Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1179Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1179Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1179Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,4,5,6,7,3,2,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,6,7,2,3,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1179Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1179Generator0 else node1179Generator1) else (if j.val < 3 then node1179Generator2 else (if j.val < 4 then node1179Generator3 else node1179Generator4)))

def node1180Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1180Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1180Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1180Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1180Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1180Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1180Generator0 else node1180Generator1) else (if j.val < 3 then node1180Generator2 else (if j.val < 4 then node1180Generator3 else node1180Generator4)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
