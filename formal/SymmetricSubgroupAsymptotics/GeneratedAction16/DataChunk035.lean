import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1120 through 1151. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1353Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,13,12,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1353Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,13,12,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1353Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,7,6,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1353Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1353Generator0 else (if j.val < 2 then node1353Generator1 else node1353Generator2))

def node1354Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,3,2,1,0,7,6,5,4,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,11,10,9,8,14,15,12,13,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1354Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,7,6,10,11,9,8,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,7,6,11,10,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1354Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,14,15,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,12,13,14,15,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1354Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1354Generator0 else (if j.val < 2 then node1354Generator1 else node1354Generator2))

def node1355Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,1,0,7,6,14,15,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,1,0,7,6,14,15,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1355Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,3,2,4,5,10,11,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,6,7,0,1,15,14,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1355Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1355Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1355Generator0 else (if j.val < 2 then node1355Generator1 else node1355Generator2))

def node1356Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,8,9,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,9,8,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1356Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,0,1,13,12,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,0,1,15,14,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1356Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,7,6,4,5,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,6,7,5,4,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1356Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1356Generator0 else (if j.val < 2 then node1356Generator1 else node1356Generator2))

def node1357Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,2,3,0,1,7,6,4,5,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,10,11,9,8,13,12,14,15,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1357Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,3,2,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1357Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1357Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1357Generator0 else (if j.val < 2 then node1357Generator1 else node1357Generator2))

def node1358Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,4,5,15,14,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,4,5,10,11,13,12,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1358Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1358Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,1,0,6,7,9,8,14,15,13,12,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,1,0,6,7,9,8,15,14,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1358Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1358Generator0 else (if j.val < 2 then node1358Generator1 else node1358Generator2))

def node1359Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,11,10,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1359Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,10,11,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1359Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1359Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1359Generator0 else (if j.val < 2 then node1359Generator1 else node1359Generator2))

def node1360Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,9,8,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,9,8,11,10,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1360Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,11,10,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,10,11,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1360Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,12,13,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1360Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1360Generator0 else (if j.val < 2 then node1360Generator1 else node1360Generator2))

def node1361Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,12,13,14,15,10,11,9,8,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,13,12,15,14,11,10,8,9,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1361Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,15,14,13,12,8,9,10,11,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,14,15,12,13,8,9,10,11,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1361Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,11,10,8,9,13,12,15,14,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,3,2,6,7,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1361Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1361Generator0 else (if j.val < 2 then node1361Generator1 else node1361Generator2))

def node1362Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1362Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,14,15,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1362Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,2,3,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,2,3,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1362Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1362Generator0 else (if j.val < 2 then node1362Generator1 else node1362Generator2))

def node1363Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,12,13,14,15,2,3,0,1,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,3,2,0,1,14,15,13,12,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1363Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,12,13,15,14,2,3,1,0,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,0,1,2,3,12,13,14,15,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1363Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,4,5,7,6,11,10,8,9,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,4,5,7,6,10,11,9,8,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1363Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1363Generator0 else (if j.val < 2 then node1363Generator1 else node1363Generator2))

def node1364Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,9,8,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1364Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,4,5,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,11,10,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1364Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1364Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1364Generator0 else (if j.val < 2 then node1364Generator1 else node1364Generator2))

def node1365Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,4,5,2,3,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,4,5,3,2,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1365Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,5,4,10,11,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,4,5,10,11,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1365Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,9,8,15,14,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1365Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1365Generator0 else (if j.val < 2 then node1365Generator1 else node1365Generator2))

def node1366Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1366Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1366Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,3,2,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,3,2,0,1,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1366Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,6,7,5,4,2,3,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,7,6,4,5,3,2,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1366Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,13,12,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1366Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1366Generator0 else node1366Generator1) else (if j.val < 3 then node1366Generator2 else (if j.val < 4 then node1366Generator3 else node1366Generator4)))

def node1367Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1367Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1367Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1367Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1367Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,8,9,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1367Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1367Generator0 else node1367Generator1) else (if j.val < 3 then node1367Generator2 else (if j.val < 4 then node1367Generator3 else node1367Generator4)))

def node1368Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,11,10,3,2,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,12,13,1,0,7,6,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1368Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,13,12,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,12,13,11,10,9,8,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1368Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1368Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1368Generator0 else (if j.val < 2 then node1368Generator1 else node1368Generator2))

def node1369Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,8,9,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,6,7,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1369Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1369Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1369Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1369Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,6,7,8,9,11,10,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,6,7,8,9,11,10,13,12,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1369Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1369Generator0 else node1369Generator1) else (if j.val < 3 then node1369Generator2 else (if j.val < 4 then node1369Generator3 else node1369Generator4)))

def node1370Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,2,3,0,1,7,6,5,4,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,11,10,9,8,15,14,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1370Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,1,0,15,14,4,5,2,3,9,8,7,6,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,8,9,6,7,13,12,11,10,1,0,15,14,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1370Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,7,6,13,12,11,10,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,9,8,6,7,13,12,11,10,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1370Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1370Generator0 else (if j.val < 2 then node1370Generator1 else node1370Generator2))

def node1371Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,8,9,11,10,14,15,13,12,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,3,2,0,1,4,5,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1371Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1371Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1371Generator0 else node1371Generator1)

def node1372Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,2,3,12,13,6,7,1,0,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,2,3,13,12,6,7,1,0,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1372Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,9,8,7,6,13,12,10,11,1,0,14,15,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,0,1,15,14,5,4,3,2,8,9,7,6,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1372Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,0,1,2,3,4,5,6,7,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,10,11,12,13,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1372Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1372Generator0 else (if j.val < 2 then node1372Generator1 else node1372Generator2))

def node1373Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,9,8,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1373Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,2,3,5,4,15,14,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,7,6,0,1,11,10,13,12,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1373Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1373Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1373Generator0 else (if j.val < 2 then node1373Generator1 else node1373Generator2))

def node1374Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1374Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,3,2,4,5,13,12,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,6,7,1,0,13,12,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1374Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,9,8,4,5,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,11,10,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1374Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1374Generator0 else (if j.val < 2 then node1374Generator1 else node1374Generator2))

def node1375Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,14,15,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1375Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1375Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1375Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1375Generator0 else (if j.val < 2 then node1375Generator1 else node1375Generator2))

def node1376Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,9,8,10,11,15,14,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,1,0,3,2,5,4,6,7,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1376Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,5,4,7,6,10,11,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,5,4,7,6,11,10,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1376Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,1,0,3,2,5,4,7,6,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,9,8,11,10,13,12,15,14,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1376Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1376Generator0 else (if j.val < 2 then node1376Generator1 else node1376Generator2))

def node1377Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,5,4,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,4,5,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1377Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1377Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,13,12,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,12,13,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1377Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1377Generator0 else (if j.val < 2 then node1377Generator1 else node1377Generator2))

def node1378Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1378Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,10,11,12,13,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,10,11,12,13,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1378Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1378Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,6,7,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,8,9,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1378Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1378Generator0 else node1378Generator1) else (if j.val < 3 then node1378Generator2 else node1378Generator3))

def node1379Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,10,11,5,4,15,14,1,0,2,3,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,7,6,0,1,3,2,4,5,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1379Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,11,10,5,4,14,15,0,1,2,3,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,7,6,0,1,3,2,5,4,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1379Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,7,6,9,8,2,3,4,5,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,8,9,3,2,5,4,14,15,0,1,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1379Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1379Generator0 else (if j.val < 2 then node1379Generator1 else node1379Generator2))

def node1380Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,8,9,5,4,6,7,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,9,8,10,11,6,7,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1380Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,8,9,10,11,4,5,6,7,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,8,9,10,11,4,5,6,7,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1380Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,12,13,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1380Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1380Generator0 else (if j.val < 2 then node1380Generator1 else node1380Generator2))

def node1381Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,9,8,2,3,4,5,15,14,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,8,9,2,3,5,4,14,15,0,1,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1381Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,0,1,13,12,11,10,8,9,6,7,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,12,13,10,11,9,8,7,6,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1381Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,11,10,12,13,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1381Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1381Generator0 else (if j.val < 2 then node1381Generator1 else node1381Generator2))

def node1382Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,14,15,12,13,0,1,2,3,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,2,3,1,0,13,12,14,15,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1382Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,10,11,6,7,4,5,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,10,11,8,9,5,4,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1382Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,15,14,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,15,14,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1382Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1382Generator0 else (if j.val < 2 then node1382Generator1 else node1382Generator2))

def node1383Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,10,11,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1383Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,10,11,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1383Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1383Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1383Generator0 else (if j.val < 2 then node1383Generator1 else node1383Generator2))

def node1384Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1384Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1384Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1384Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1384Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1384Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1384Generator0 else node1384Generator1) else (if j.val < 3 then node1384Generator2 else (if j.val < 4 then node1384Generator3 else node1384Generator4)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
