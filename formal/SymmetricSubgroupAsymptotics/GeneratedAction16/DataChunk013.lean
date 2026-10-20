import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
416 through 447. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node480Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node480Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,10,11,8,9,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,11,10,9,8,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node480Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,1,0,2,3,15,14,12,13,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,13,12,14,15,2,3,1,0,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node480Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node480Generator0 else (if j.val < 2 then node480Generator1 else node480Generator2))

def node481Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node481Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node481Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node481Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node481Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node481Generator0 else node481Generator1) else (if j.val < 3 then node481Generator2 else node481Generator3))

def node482Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,11,10,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node482Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,3,2,5,4,10,11,13,12,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,7,6,0,1,15,14,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node482Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node482Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node482Generator0 else (if j.val < 2 then node482Generator1 else node482Generator2))

def node483Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,13,12,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node483Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,8,9,10,11,15,14,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,3,2,1,0,4,5,6,7,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node483Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,4,5,6,7,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,4,5,6,7,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node483Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node483Generator0 else (if j.val < 2 then node483Generator1 else node483Generator2))

def node484Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node484Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node484Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node484Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node484Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node484Generator0 else node484Generator1) else (if j.val < 3 then node484Generator2 else node484Generator3))

def node485Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,10,11,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node485Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,9,8,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node485Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,11,10,13,12,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node485Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node485Generator0 else (if j.val < 2 then node485Generator1 else node485Generator2))

def node486Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node486Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node486Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node486Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node486Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node486Generator0 else node486Generator1) else (if j.val < 3 then node486Generator2 else node486Generator3))

def node487Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,11,10,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,15,14,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node487Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,9,8,14,15,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node487Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node487Generator0 else node487Generator1)

def node488Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,7,6,4,5,11,10,8,9,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,6,7,5,4,10,11,9,8,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node488Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node488Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node488Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node488Generator0 else (if j.val < 2 then node488Generator1 else node488Generator2))

def node489Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,4,5,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node489Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node489Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node489Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node489Generator0 else (if j.val < 2 then node489Generator1 else node489Generator2))

def node490Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,11,10,8,9,14,15,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,1,0,3,2,6,7,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node490Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,2,3,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node490Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,8,9,11,10,13,12,14,15,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,2,3,0,1,4,5,7,6,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node490Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node490Generator0 else (if j.val < 2 then node490Generator1 else node490Generator2))

def node491Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,5,4,6,7,1,0,2,3,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,5,4,6,7,0,1,3,2,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node491Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,11,10,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,8,9,4,5,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node491Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,3,2,1,0,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,0,1,3,2,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node491Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node491Generator0 else (if j.val < 2 then node491Generator1 else node491Generator2))

def node492Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,6,7,4,5,11,10,9,8,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,6,7,4,5,11,10,9,8,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node492Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,13,12,14,15,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node492Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,15,14,13,12,1,0,3,2,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,3,2,1,0,12,13,14,15,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node492Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node492Generator0 else (if j.val < 2 then node492Generator1 else node492Generator2))

def node493Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node493Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node493Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node493Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node493Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node493Generator0 else node493Generator1) else (if j.val < 3 then node493Generator2 else node493Generator3))

def node494Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node494Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,1,0,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node494Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node494Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,9,8,5,4,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,11,10,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node494Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node494Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node494Generator0 else node494Generator1) else (if j.val < 3 then node494Generator2 else (if j.val < 4 then node494Generator3 else node494Generator4)))

def node495Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,10,11,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node495Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,8,9,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,6,7,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node495Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node495Generator0 else node495Generator1)

def node496Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node496Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node496Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node496Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node496Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node496Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node496Generator0 else node496Generator1) else (if j.val < 3 then node496Generator2 else (if j.val < 4 then node496Generator3 else node496Generator4)))

def node497Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node497Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,0,1,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,2,3,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node497Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,1,0,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node497Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,12,13,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node497Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node497Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node497Generator0 else node497Generator1) else (if j.val < 3 then node497Generator2 else (if j.val < 4 then node497Generator3 else node497Generator4)))

def node498Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node498Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node498Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,11,10,8,9,15,14,12,13,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,0,1,2,3,6,7,5,4,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node498Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,4,5,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,11,10,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node498Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node498Generator0 else node498Generator1) else (if j.val < 3 then node498Generator2 else node498Generator3))

def node499Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,0,1,2,3,4,5,6,7,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,10,11,15,14,12,13,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node499Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node499Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,1,0,3,2,6,7,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,11,10,8,9,14,15,13,12,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node499Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node499Generator0 else (if j.val < 2 then node499Generator1 else node499Generator2))

def node500Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,11,10,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,15,14,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node500Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node500Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node500Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node500Generator0 else (if j.val < 2 then node500Generator1 else node500Generator2))

def node501Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node501Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,2,3,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,1,0,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node501Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,13,12,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,14,15,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node501Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node501Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,9,8,5,4,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,11,10,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node501Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node501Generator0 else node501Generator1) else (if j.val < 3 then node501Generator2 else (if j.val < 4 then node501Generator3 else node501Generator4)))

def node502Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node502Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node502Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,1,0,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node502Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node502Generator0 else (if j.val < 2 then node502Generator1 else node502Generator2))

def node503Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,3,2,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node503Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,8,9,11,10,5,4,6,7,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,9,8,10,11,4,5,7,6,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node503Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,7,6,4,5,11,10,8,9,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,6,7,5,4,10,11,9,8,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node503Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node503Generator0 else (if j.val < 2 then node503Generator1 else node503Generator2))

def node504Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,7,6,4,5,9,8,11,10,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,6,7,5,4,9,8,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node504Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node504Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,7,6,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,7,6,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node504Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node504Generator0 else (if j.val < 2 then node504Generator1 else node504Generator2))

def node505Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,11,10,9,8,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,10,11,8,9,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node505Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,4,5,7,6,8,9,11,10,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,4,5,7,6,8,9,11,10,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node505Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,14,15,12,13,0,1,2,3,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,3,2,1,0,12,13,14,15,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node505Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node505Generator0 else (if j.val < 2 then node505Generator1 else node505Generator2))

def node506Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node506Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node506Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node506Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node506Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node506Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node506Generator0 else node506Generator1) else (if j.val < 3 then node506Generator2 else (if j.val < 4 then node506Generator3 else node506Generator4)))

def node507Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node507Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node507Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,6,7,5,4,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,7,6,4,5,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node507Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,3,2,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,0,1,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node507Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node507Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node507Generator0 else node507Generator1) else (if j.val < 3 then node507Generator2 else (if j.val < 4 then node507Generator3 else node507Generator4)))

def node508Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node508Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,7,6,10,11,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,7,6,11,10,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node508Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node508Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node508Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node508Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node508Generator0 else node508Generator1) else (if j.val < 3 then node508Generator2 else (if j.val < 4 then node508Generator3 else node508Generator4)))

def node509Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,15,14,8,9,10,11,12,13,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,15,14,8,9,10,11,12,13,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node509Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,13,12,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,13,12,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node509Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,5,4,7,6,1,0,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,3,2,5,4,7,6,1,0,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node509Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node509Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node509Generator0 else node509Generator1) else (if j.val < 3 then node509Generator2 else node509Generator3))

def node510Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,4,5,3,2,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,4,5,3,2,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node510Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node510Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node510Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node510Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node510Generator0 else node510Generator1) else (if j.val < 3 then node510Generator2 else node510Generator3))

def node511Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,4,5,2,3,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node511Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node511Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node511Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node511Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node511Generator0 else node511Generator1) else (if j.val < 3 then node511Generator2 else node511Generator3))

end SymmetricSubgroupAsymptotics.BinaryActionData16
