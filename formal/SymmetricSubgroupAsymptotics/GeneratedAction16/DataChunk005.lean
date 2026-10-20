import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
160 through 191. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node171Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,2,3,13,12,6,7,1,0,10,11,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,4,5,15,14,8,9,3,2,12,13,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node171Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,8,9,14,15,12,13,10,11,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,0,1,14,15,12,13,2,3,8,9,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node171Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node171Generator0 else node171Generator1)

def node172Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,4,5,3,2,1,0,6,7,12,13,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,7,6,4,5,10,11,1,0,15,14,12,13,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node172Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,0,1,10,11,12,13,7,6,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,0,1,2,3,13,12,14,15,8,9,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node172Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node172Generator0 else node172Generator1)

def node173Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,8,9,10,11,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,11,10,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node173Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node173Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node173Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node173Generator0 else (if j.val < 2 then node173Generator1 else node173Generator2))

def node174Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,11,10,9,8,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,2,3,1,0,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node174Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node174Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node174Generator0 else node174Generator1)

def node175Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,13,12,14,15,10,11,9,8,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,13,12,14,15,11,10,8,9,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node175Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,10,11,8,9,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,2,3,1,0,6,7,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node175Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,8,9,11,10,4,5,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,8,9,11,10,4,5,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node175Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node175Generator0 else (if j.val < 2 then node175Generator1 else node175Generator2))

def node176Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,0,1,13,12,7,6,9,8,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,1,0,9,8,11,10,13,12,7,6,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node176Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,13,12,10,11,4,5,2,3,0,1,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,6,7,0,1,15,14,4,5,3,2,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node176Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node176Generator0 else node176Generator1)

def node177Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,7,6,4,5,3,2,1,0,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,6,7,5,4,3,2,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node177Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,13,12,14,15,10,11,9,8,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,12,13,15,14,11,10,8,9,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node177Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,10,11,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,11,10,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node177Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node177Generator0 else (if j.val < 2 then node177Generator1 else node177Generator2))

def node197Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node197Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node197Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node197Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node197Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node197Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node197Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node197Generator0 else (if j.val < 2 then node197Generator1 else node197Generator2)) else (if j.val < 4 then node197Generator3 else (if j.val < 5 then node197Generator4 else node197Generator5)))

def node198Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node198Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node198Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node198Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,2,3,4,5,1,0,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,2,3,4,5,1,0,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node198Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,15,14,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,14,15,4,5,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node198Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node198Generator0 else node198Generator1) else (if j.val < 3 then node198Generator2 else (if j.val < 4 then node198Generator3 else node198Generator4)))

def node199Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node199Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,3,2,0,1,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node199Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node199Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,10,11,5,4,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,11,10,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node199Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node199Generator0 else node199Generator1) else (if j.val < 3 then node199Generator2 else node199Generator3))

def node200Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node200Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node200Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node200Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node200Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node200Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node200Generator0 else node200Generator1) else (if j.val < 3 then node200Generator2 else (if j.val < 4 then node200Generator3 else node200Generator4)))

def node201Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node201Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node201Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node201Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,2,3,4,5,1,0,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,2,3,4,5,1,0,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node201Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,12,13,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node201Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node201Generator0 else node201Generator1) else (if j.val < 3 then node201Generator2 else (if j.val < 4 then node201Generator3 else node201Generator4)))

def node202Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node202Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node202Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node202Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node202Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node202Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node202Generator0 else node202Generator1) else (if j.val < 3 then node202Generator2 else (if j.val < 4 then node202Generator3 else node202Generator4)))

def node203Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node203Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node203Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node203Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node203Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,5,4,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,11,10,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node203Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node203Generator0 else node203Generator1) else (if j.val < 3 then node203Generator2 else (if j.val < 4 then node203Generator3 else node203Generator4)))

def node204Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node204Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node204Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node204Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node204Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node204Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node204Generator0 else node204Generator1) else (if j.val < 3 then node204Generator2 else (if j.val < 4 then node204Generator3 else node204Generator4)))

def node205Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node205Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,5,4,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,4,5,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node205Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node205Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node205Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node205Generator0 else node205Generator1) else (if j.val < 3 then node205Generator2 else node205Generator3))

def node206Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node206Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node206Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node206Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,2,3,4,5,1,0,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,2,3,4,5,1,0,8,9,10,11,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node206Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,12,13,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node206Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node206Generator0 else node206Generator1) else (if j.val < 3 then node206Generator2 else (if j.val < 4 then node206Generator3 else node206Generator4)))

def node207Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node207Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node207Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node207Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node207Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node207Generator0 else node207Generator1) else (if j.val < 3 then node207Generator2 else node207Generator3))

def node208Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,0,1,14,15,12,13,2,3,8,9,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,8,9,15,14,13,12,10,11,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node208Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,12,13,10,11,9,8,15,14,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,1,0,7,6,4,5,2,3,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node208Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,3,2,0,1,6,7,5,4,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,11,10,8,9,14,15,12,13,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node208Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node208Generator0 else (if j.val < 2 then node208Generator1 else node208Generator2))

def node209Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,7,6,4,5,10,11,9,8,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,6,7,5,4,11,10,8,9,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node209Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,8,9,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,10,11,9,8,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node209Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,12,13,14,15,2,3,0,1,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,2,3,0,1,13,12,15,14,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node209Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node209Generator0 else (if j.val < 2 then node209Generator1 else node209Generator2))

def node210Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,2,3,1,0,7,6,4,5,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,10,11,9,8,15,14,13,12,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node210Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,9,8,14,15,4,5,11,10,1,0,7,6,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,1,0,6,7,13,12,3,2,9,8,15,14,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node210Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,9,8,14,15,13,12,11,10,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,0,1,7,6,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node210Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node210Generator0 else (if j.val < 2 then node210Generator1 else node210Generator2))

def node211Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node211Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,0,1,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,5,4,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node211Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node211Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node211Generator0 else (if j.val < 2 then node211Generator1 else node211Generator2))

def node212Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node212Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,8,9,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node212Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node212Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node212Generator0 else (if j.val < 2 then node212Generator1 else node212Generator2))

def node213Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node213Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,2,3,0,1,13,12,15,14,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,12,13,14,15,3,2,1,0,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node213Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,14,15,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node213Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node213Generator0 else (if j.val < 2 then node213Generator1 else node213Generator2))

def node214Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node214Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node214Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node214Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,9,8,6,7,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,8,9,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node214Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node214Generator0 else node214Generator1) else (if j.val < 3 then node214Generator2 else node214Generator3))

def node215Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,8,9,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node215Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,9,8,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,8,9,10,11,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node215Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node215Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node215Generator0 else (if j.val < 2 then node215Generator1 else node215Generator2))

def node216Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,0,1,3,2,14,15,13,12,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,14,15,13,12,1,0,2,3,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node216Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,8,9,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,10,11,9,8,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node216Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,6,7,4,5,10,11,8,9,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,6,7,4,5,10,11,8,9,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node216Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node216Generator0 else (if j.val < 2 then node216Generator1 else node216Generator2))

def node217Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,13,12,11,10,8,9,15,14,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,14,15,4,5,10,11,9,8,7,6,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node217Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,11,10,13,12,14,15,8,9,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,11,10,13,12,14,15,8,9,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node217Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,1,0,3,2,4,5,6,7,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,8,9,10,11,12,13,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node217Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node217Generator0 else (if j.val < 2 then node217Generator1 else node217Generator2))

def node218Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,8,9,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node218Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node218Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,13,12,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,10,11,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node218Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node218Generator0 else (if j.val < 2 then node218Generator1 else node218Generator2))

def node219Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,6,7,5,4,9,8,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,7,6,4,5,9,8,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node219Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,9,8,11,10,14,15,12,13,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,1,0,2,3,5,4,7,6,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node219Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node219Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node219Generator0 else (if j.val < 2 then node219Generator1 else node219Generator2))

def node220Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,1,0,3,2,4,5,6,7,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,8,9,10,11,14,15,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node220Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,1,0,3,2,6,7,5,4,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,11,10,8,9,15,14,12,13,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node220Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,8,9,10,11,14,15,13,12,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,0,1,2,3,4,5,6,7,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node220Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node220Generator0 else (if j.val < 2 then node220Generator1 else node220Generator2))

def node221Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,13,12,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,11,10,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node221Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node221Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,8,9,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node221Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node221Generator0 else (if j.val < 2 then node221Generator1 else node221Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
