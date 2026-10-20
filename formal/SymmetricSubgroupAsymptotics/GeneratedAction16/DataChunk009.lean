import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
288 through 319. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node318Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,9,8,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,9,8,11,10,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node318Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node318Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,15,14,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,15,14,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node318Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node318Generator0 else (if j.val < 2 then node318Generator1 else node318Generator2))

def node319Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,3,2,5,4,9,8,14,15,12,13,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,7,6,1,0,9,8,15,14,12,13,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node319Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,11,10,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node319Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,14,15,4,5,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,15,14,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node319Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node319Generator0 else (if j.val < 2 then node319Generator1 else node319Generator2))

def node320Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node320Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,1,0,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node320Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node320Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,10,11,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,11,10,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node320Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node320Generator0 else node320Generator1) else (if j.val < 3 then node320Generator2 else node320Generator3))

def node321Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node321Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,7,6,4,5,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,5,4,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node321Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,9,8,11,10,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,8,9,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node321Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node321Generator0 else (if j.val < 2 then node321Generator1 else node321Generator2))

def node322Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,10,11,8,9,14,15,13,12,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,0,1,2,3,6,7,4,5,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node322Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,4,5,6,7,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,4,5,6,7,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node322Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,1,0,3,2,7,6,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,11,10,9,8,14,15,13,12,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node322Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node322Generator0 else (if j.val < 2 then node322Generator1 else node322Generator2))

def node323Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,0,1,11,10,13,12,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,0,1,2,3,4,5,14,15,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node323Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,14,15,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,11,10,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node323Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node323Generator0 else node323Generator1)

def node324Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,8,9,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,8,9,10,11,6,7,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node324Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node324Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,13,12,14,15,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node324Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node324Generator0 else (if j.val < 2 then node324Generator1 else node324Generator2))

def node325Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node325Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node325Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node325Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,15,14,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,14,15,4,5,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node325Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node325Generator0 else node325Generator1) else (if j.val < 3 then node325Generator2 else node325Generator3))

def node326Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,13,12,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node326Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,4,5,7,6,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,4,5,7,6,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node326Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,1,0,2,3,15,14,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,1,0,12,13,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node326Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node326Generator0 else (if j.val < 2 then node326Generator1 else node326Generator2))

def node327Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,5,4,8,9,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,4,5,8,9,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node327Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,1,0,3,2,7,6,5,4,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,11,10,9,8,15,14,12,13,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node327Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,12,13,2,3,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,12,13,2,3,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node327Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node327Generator0 else (if j.val < 2 then node327Generator1 else node327Generator2))

def node328Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node328Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,5,4,3,2,6,7,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,5,4,3,2,6,7,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node328Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node328Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node328Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node328Generator0 else node328Generator1) else (if j.val < 3 then node328Generator2 else node328Generator3))

def node329Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node329Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node329Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node329Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,12,13,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node329Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node329Generator0 else node329Generator1) else (if j.val < 3 then node329Generator2 else node329Generator3))

def node330Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,15,14,5,4,10,11,9,8,7,6,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,13,12,11,10,8,9,15,14,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node330Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,8,9,10,11,13,12,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,5,4,6,7,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node330Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node330Generator0 else node330Generator1)

def node331Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,8,9,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,8,9,11,10,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node331Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,9,8,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,10,11,9,8,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node331Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node331Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node331Generator0 else (if j.val < 2 then node331Generator1 else node331Generator2))

def node332Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node332Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,10,11,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,13,12,11,10,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node332Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node332Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node332Generator0 else (if j.val < 2 then node332Generator1 else node332Generator2))

def node333Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,0,1,11,10,4,5,15,14,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,8,9,2,3,12,13,7,6,0,1,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node333Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,8,9,2,3,12,13,14,15,0,1,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,6,7,0,1,3,2,4,5,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node333Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,0,1,7,6,13,12,2,3,9,8,15,14,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,8,9,15,14,5,4,11,10,1,0,7,6,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node333Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node333Generator0 else (if j.val < 2 then node333Generator1 else node333Generator2))

def node334Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,5,4,7,6,8,9,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,5,4,7,6,8,9,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node334Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,15,14,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,15,14,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node334Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node334Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node334Generator0 else (if j.val < 2 then node334Generator1 else node334Generator2))

def node335Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,6,7,0,1,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node335Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,10,11,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node335Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node335Generator0 else node335Generator1)

def node336Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node336Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,5,4,6,7,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,6,7,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node336Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node336Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node336Generator0 else (if j.val < 2 then node336Generator1 else node336Generator2))

def node337Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,8,9,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,9,8,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node337Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node337Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node337Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node337Generator0 else (if j.val < 2 then node337Generator1 else node337Generator2))

def node338Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node338Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,8,9,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,15,14,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node338Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node338Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node338Generator0 else (if j.val < 2 then node338Generator1 else node338Generator2))

def node339Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,5,4,15,14,9,8,2,3,12,13,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,3,2,12,13,7,6,1,0,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node339Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,15,14,5,4,11,10,9,8,6,7,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,12,13,11,10,9,8,14,15,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node339Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node339Generator0 else node339Generator1)

def node340Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node340Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,13,12,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node340Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,10,11,9,8,7,6,4,5,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,10,11,9,8,7,6,4,5,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node340Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node340Generator0 else (if j.val < 2 then node340Generator1 else node340Generator2))

def node341Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,6,7,2,3,4,5,14,15,0,1,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,6,7,8,9,4,5,3,2,1,0,14,15,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node341Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,0,1,8,9,11,10,12,13,7,6,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,1,0,13,12,6,7,9,8,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node341Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,6,7,15,14,5,4,3,2,1,0,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,4,5,14,15,1,0,3,2,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node341Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node341Generator0 else (if j.val < 2 then node341Generator1 else node341Generator2))

def node342Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,10,11,8,9,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,11,10,9,8,6,7,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node342Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node342Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,3,2,0,1,13,12,14,15,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,13,12,14,15,3,2,0,1,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node342Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node342Generator0 else (if j.val < 2 then node342Generator1 else node342Generator2))

def node343Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,14,15,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node343Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node343Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node343Generator0 else node343Generator1)

def node344Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node344Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,8,9,6,7,5,4,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,11,10,8,9,6,7,5,4,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node344Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,3,2,1,0,12,13,14,15,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,13,12,15,14,2,3,0,1,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node344Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node344Generator0 else (if j.val < 2 then node344Generator1 else node344Generator2))

def node345Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,1,0,2,3,14,15,13,12,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,14,15,13,12,0,1,3,2,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node345Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,7,6,4,5,10,11,9,8,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,6,7,5,4,11,10,8,9,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node345Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,12,13,14,15,2,3,0,1,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,3,2,1,0,13,12,15,14,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node345Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node345Generator0 else (if j.val < 2 then node345Generator1 else node345Generator2))

def node346Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,13,12,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node346Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node346Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node346Generator0 else node346Generator1)

def node347Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,0,1,11,10,4,5,15,14,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,8,9,2,3,12,13,7,6,0,1,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node347Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,11,10,9,8,14,15,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,0,1,7,6,5,4,2,3,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node347Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,8,9,11,10,12,13,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,0,1,10,11,4,5,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node347Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node347Generator0 else (if j.val < 2 then node347Generator1 else node347Generator2))

def node348Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node348Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,3,2,0,1,4,5,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,8,9,10,11,12,13,14,15,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node348Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node348Generator0 else node348Generator1)

def node349Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,9,8,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,9,8,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node349Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node349Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node349Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node349Generator0 else (if j.val < 2 then node349Generator1 else node349Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
