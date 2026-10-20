import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
544 through 575. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node608Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node608Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node608Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node608Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node608Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,7,6,5,4,2,3,0,1,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,7,6,5,4,3,2,1,0,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node608Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node608Generator0 else node608Generator1) else (if j.val < 3 then node608Generator2 else (if j.val < 4 then node608Generator3 else node608Generator4)))

def node609Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,5,4,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,11,10,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node609Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,13,12,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node609Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,10,11,9,8,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,11,10,7,6,4,5,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node609Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node609Generator0 else (if j.val < 2 then node609Generator1 else node609Generator2))

def node610Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,4,5,3,2,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,6,7,5,4,2,3,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node610Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,3,2,12,13,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,3,2,0,1,15,14,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node610Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,8,9,10,11,12,13,14,15,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,2,3,1,0,4,5,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node610Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node610Generator0 else (if j.val < 2 then node610Generator1 else node610Generator2))

def node611Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,6,7,9,8,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,6,7,9,8,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node611Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,8,9,10,11,14,15,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,2,3,0,1,4,5,6,7,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node611Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node611Generator0 else node611Generator1)

def node612Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,1,0,2,3,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,3,2,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node612Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,13,12,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node612Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node612Generator0 else node612Generator1)

def node613Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node613Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node613Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node613Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node613Generator0 else (if j.val < 2 then node613Generator1 else node613Generator2))

def node614Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,10,11,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node614Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node614Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,13,12,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node614Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node614Generator0 else (if j.val < 2 then node614Generator1 else node614Generator2))

def node615Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,13,12,15,14,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,9,8,3,2,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node615Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,10,11,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,13,12,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node615Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node615Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node615Generator0 else (if j.val < 2 then node615Generator1 else node615Generator2))

def node616Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node616Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node616Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node616Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,14,15,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,12,13,14,15,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node616Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,10,11,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node616Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node616Generator0 else node616Generator1) else (if j.val < 3 then node616Generator2 else (if j.val < 4 then node616Generator3 else node616Generator4)))

def node617Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,13,12,15,14,3,2,1,0,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,3,2,1,0,12,13,14,15,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node617Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,10,11,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,10,11,4,5,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node617Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,7,6,4,5,11,10,8,9,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,6,7,5,4,10,11,9,8,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node617Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node617Generator0 else (if j.val < 2 then node617Generator1 else node617Generator2))

def node618Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node618Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node618Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node618Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node618Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node618Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node618Generator0 else node618Generator1) else (if j.val < 3 then node618Generator2 else (if j.val < 4 then node618Generator3 else node618Generator4)))

def node619Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,13,12,15,14,1,0,2,3,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,3,2,0,1,15,14,13,12,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node619Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,3,2,1,0,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,0,1,3,2,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node619Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node619Generator0 else node619Generator1)

def node620Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,15,14,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node620Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,13,12,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,15,14,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node620Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node620Generator0 else node620Generator1)

def node621Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,8,9,15,14,11,10,1,0,4,5,3,2,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,13,12,10,11,14,15,2,3,7,6,0,1,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node621Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node621Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,14,15,9,8,12,13,2,3,7,6,1,0,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,8,9,14,15,11,10,5,4,1,0,6,7,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node621Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node621Generator0 else (if j.val < 2 then node621Generator1 else node621Generator2))

def node622Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node622Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,1,0,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,2,3,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node622Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,1,0,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node622Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,1,0,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,12,13,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node622Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node622Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node622Generator0 else node622Generator1) else (if j.val < 3 then node622Generator2 else (if j.val < 4 then node622Generator3 else node622Generator4)))

def node623Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,5,4,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,5,4,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node623Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,11,10,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node623Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,14,15,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node623Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node623Generator0 else (if j.val < 2 then node623Generator1 else node623Generator2))

def node624Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,3,2,0,1,6,7,5,4,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,11,10,8,9,12,13,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node624Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,1,0,2,3,4,5,6,7,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,8,9,10,11,14,15,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node624Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node624Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node624Generator0 else (if j.val < 2 then node624Generator1 else node624Generator2))

def node625Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node625Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,2,3,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,3,2,0,1,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node625Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node625Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,9,8,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,8,9,7,6,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node625Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node625Generator0 else node625Generator1) else (if j.val < 3 then node625Generator2 else node625Generator3))

def node626Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node626Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node626Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,14,15,13,12,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,11,10,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node626Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node626Generator0 else (if j.val < 2 then node626Generator1 else node626Generator2))

def node627Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,13,12,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node627Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,13,12,15,14,1,0,2,3,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,2,3,1,0,14,15,12,13,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node627Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node627Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node627Generator0 else (if j.val < 2 then node627Generator1 else node627Generator2))

def node628Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node628Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node628Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node628Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,2,3,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,3,2,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node628Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node628Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node628Generator0 else node628Generator1) else (if j.val < 3 then node628Generator2 else (if j.val < 4 then node628Generator3 else node628Generator4)))

def node629Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,11,10,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node629Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,9,8,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node629Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,10,11,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node629Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node629Generator0 else (if j.val < 2 then node629Generator1 else node629Generator2))

def node630Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,3,2,1,0,13,12,15,14,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,15,14,13,12,0,1,2,3,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node630Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,6,7,4,5,11,10,9,8,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,6,7,4,5,11,10,9,8,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node630Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,6,7,9,8,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,6,7,9,8,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node630Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node630Generator0 else (if j.val < 2 then node630Generator1 else node630Generator2))

def node631Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,1,0,2,3,15,14,12,13,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,14,15,13,12,1,0,2,3,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node631Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,10,11,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,10,11,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node631Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node631Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node631Generator0 else (if j.val < 2 then node631Generator1 else node631Generator2))

def node632Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node632Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node632Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node632Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node632Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node632Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node632Generator0 else node632Generator1) else (if j.val < 3 then node632Generator2 else (if j.val < 4 then node632Generator3 else node632Generator4)))

def node633Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node633Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,0,1,14,15,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,5,4,11,10,13,12,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node633Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node633Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node633Generator0 else (if j.val < 2 then node633Generator1 else node633Generator2))

def node634Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node634Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node634Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node634Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node634Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,12,13,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node634Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node634Generator0 else node634Generator1) else (if j.val < 3 then node634Generator2 else (if j.val < 4 then node634Generator3 else node634Generator4)))

def node635Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node635Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node635Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node635Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,2,3,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,0,1,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node635Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node635Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node635Generator0 else node635Generator1) else (if j.val < 3 then node635Generator2 else (if j.val < 4 then node635Generator3 else node635Generator4)))

def node636Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node636Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,3,2,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,3,2,0,1,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node636Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node636Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,9,8,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,7,6,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node636Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node636Generator0 else node636Generator1) else (if j.val < 3 then node636Generator2 else node636Generator3))

def node637Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,8,9,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node637Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,2,3,14,15,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,0,1,13,12,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node637Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node637Generator0 else node637Generator1)

def node638Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node638Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node638Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node638Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,2,3,13,12,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,0,1,15,14,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node638Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node638Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node638Generator0 else node638Generator1) else (if j.val < 3 then node638Generator2 else (if j.val < 4 then node638Generator3 else node638Generator4)))

def node639Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node639Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node639Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node639Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node639Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node639Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node639Generator0 else node639Generator1) else (if j.val < 3 then node639Generator2 else (if j.val < 4 then node639Generator3 else node639Generator4)))

end SymmetricSubgroupAsymptotics.BinaryActionData16
