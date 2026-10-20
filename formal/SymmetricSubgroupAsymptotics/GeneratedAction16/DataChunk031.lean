import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
992 through 1023. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1181Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1181Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1181Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1181Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1181Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1181Generator0 else node1181Generator1) else (if j.val < 3 then node1181Generator2 else node1181Generator3))

def node1182Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,1,0,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1182Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,10,11,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1182Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,4,5,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,8,9,11,10,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1182Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1182Generator0 else (if j.val < 2 then node1182Generator1 else node1182Generator2))

def node1183Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1183Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1183Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1183Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,11,10,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,8,9,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1183Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1183Generator0 else node1183Generator1) else (if j.val < 3 then node1183Generator2 else node1183Generator3))

def node1184Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,8,9,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1184Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,12,13,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1184Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1184Generator0 else node1184Generator1)

def node1185Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1185Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,11,10,9,8,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1185Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1185Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1185Generator0 else (if j.val < 2 then node1185Generator1 else node1185Generator2))

def node1186Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1186Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,7,6,5,4,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,7,6,5,4,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1186Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,8,9,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1186Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1186Generator0 else (if j.val < 2 then node1186Generator1 else node1186Generator2))

def node1187Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,13,12,10,11,0,1,14,15,4,5,2,3,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,12,13,10,11,0,1,15,14,4,5,3,2,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1187Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,7,6,4,5,3,2,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,6,7,5,4,2,3,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1187Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,8,9,2,3,5,4,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,9,8,2,3,4,5,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1187Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1187Generator0 else (if j.val < 2 then node1187Generator1 else node1187Generator2))

def node1188Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,0,1,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,2,3,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1188Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,11,10,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1188Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,1,0,2,3,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,1,0,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1188Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1188Generator0 else (if j.val < 2 then node1188Generator1 else node1188Generator2))

def node1189Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1189Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1189Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1189Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1189Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1189Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1189Generator0 else node1189Generator1) else (if j.val < 3 then node1189Generator2 else (if j.val < 4 then node1189Generator3 else node1189Generator4)))

def node1190Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1190Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1190Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1190Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1190Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1190Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1190Generator0 else node1190Generator1) else (if j.val < 3 then node1190Generator2 else (if j.val < 4 then node1190Generator3 else node1190Generator4)))

def node1191Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1191Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1191Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1191Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1191Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1191Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1191Generator0 else node1191Generator1) else (if j.val < 3 then node1191Generator2 else (if j.val < 4 then node1191Generator3 else node1191Generator4)))

def node1192Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,9,8,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,13,12,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1192Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1192Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1192Generator0 else node1192Generator1)

def node1193Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1193Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1193Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1193Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1193Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1193Generator0 else node1193Generator1) else (if j.val < 3 then node1193Generator2 else node1193Generator3))

def node1194Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,0,1,2,3,5,4,7,6,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,8,9,11,10,13,12,15,14,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1194Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,1,0,3,2,5,4,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,9,8,10,11,12,13,14,15,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1194Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1194Generator0 else node1194Generator1)

def node1195Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1195Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1195Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1195Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1195Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1195Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1195Generator0 else node1195Generator1) else (if j.val < 3 then node1195Generator2 else (if j.val < 4 then node1195Generator3 else node1195Generator4)))

def node1196Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1196Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,15,14,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1196Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1196Generator0 else node1196Generator1)

def node1197Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1197Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1197Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,8,9,10,11,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,2,3,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1197Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,2,3,0,1,15,14,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,6,7,13,12,14,15,5,4,3,2,0,1,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1197Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1197Generator0 else node1197Generator1) else (if j.val < 3 then node1197Generator2 else node1197Generator3))

def node1198Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1198Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,4,5,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1198Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,2,3,12,13,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,3,2,12,13,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1198Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1198Generator0 else (if j.val < 2 then node1198Generator1 else node1198Generator2))

def node1199Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,11,10,8,9,14,15,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,0,1,3,2,6,7,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1199Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,11,10,9,8,15,14,12,13,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,3,2,0,1,7,6,5,4,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1199Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1199Generator0 else node1199Generator1)

def node1200Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,3,2,4,5,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,6,7,1,0,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1200Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1200Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,13,12,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1200Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1200Generator0 else (if j.val < 2 then node1200Generator1 else node1200Generator2))

def node1201Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1201Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1201Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,3,2,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,2,3,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1201Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1201Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1201Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1201Generator0 else node1201Generator1) else (if j.val < 3 then node1201Generator2 else (if j.val < 4 then node1201Generator3 else node1201Generator4)))

def node1202Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1202Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1202Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1202Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1202Generator0 else (if j.val < 2 then node1202Generator1 else node1202Generator2))

def node1203Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1203Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1203Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1203Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1203Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1203Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1203Generator0 else node1203Generator1) else (if j.val < 3 then node1203Generator2 else (if j.val < 4 then node1203Generator3 else node1203Generator4)))

def node1204Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,9,8,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1204Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,9,8,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,7,6,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1204Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1204Generator0 else node1204Generator1)

def node1205Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,4,5,7,6,9,8,10,11,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,4,5,7,6,9,8,10,11,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1205Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,0,1,3,2,13,12,14,15,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,15,14,13,12,1,0,3,2,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1205Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1205Generator0 else node1205Generator1)

def node1206Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1206Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,3,2,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,3,2,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1206Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1206Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,10,11,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1206Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,11,10,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,8,9,5,4,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1206Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1206Generator0 else node1206Generator1) else (if j.val < 3 then node1206Generator2 else (if j.val < 4 then node1206Generator3 else node1206Generator4)))

def node1207Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,9,8,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,8,9,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1207Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1207Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1207Generator0 else node1207Generator1)

def node1208Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,1,0,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,3,2,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1208Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1208Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,13,12,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1208Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1208Generator0 else (if j.val < 2 then node1208Generator1 else node1208Generator2))

def node1209Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1209Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,7,6,11,10,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,7,6,10,11,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1209Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,7,6,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,6,7,5,4,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1209Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1209Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1209Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1209Generator0 else node1209Generator1) else (if j.val < 3 then node1209Generator2 else (if j.val < 4 then node1209Generator3 else node1209Generator4)))

def node1210Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,2,3,0,1,15,14,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,6,7,13,12,15,14,5,4,3,2,0,1,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1210Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,12,13,10,11,4,5,3,2,1,0,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,6,7,1,0,14,15,4,5,2,3,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1210Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1210Generator0 else node1210Generator1)

def node1211Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1211Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,7,6,5,4,8,9,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,7,6,5,4,8,9,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1211Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,13,12,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1211Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1211Generator0 else (if j.val < 2 then node1211Generator1 else node1211Generator2))

def node1212Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,14,15,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,13,12,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1212Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,9,8,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,11,10,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1212Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1212Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1212Generator0 else (if j.val < 2 then node1212Generator1 else node1212Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
