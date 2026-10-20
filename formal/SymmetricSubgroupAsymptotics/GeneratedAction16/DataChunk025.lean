import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
800 through 831. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node934Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node934Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,10,11,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node934Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node934Generator0 else node934Generator1)

def node935Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node935Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,9,8,11,10,4,5,6,7,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,10,11,5,4,7,6,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node935Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,3,2,15,14,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,1,0,3,2,14,15,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node935Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node935Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node935Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node935Generator0 else node935Generator1) else (if j.val < 3 then node935Generator2 else (if j.val < 4 then node935Generator3 else node935Generator4)))

def node936Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,10,11,6,7,4,5,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,10,11,8,9,5,4,6,7,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node936Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,14,15,12,13,1,0,3,2,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,1,0,3,2,13,12,14,15,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node936Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node936Generator0 else node936Generator1)

def node937Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,15,14,13,12,3,2,0,1,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,1,0,2,3,14,15,13,12,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node937Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node937Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,3,2,12,13,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,1,0,12,13,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node937Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node937Generator0 else (if j.val < 2 then node937Generator1 else node937Generator2))

def node938Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node938Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,2,3,13,12,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,0,1,15,14,12,13,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node938Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,11,10,9,8,6,7,4,5,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,10,11,8,9,7,6,5,4,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node938Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node938Generator0 else (if j.val < 2 then node938Generator1 else node938Generator2))

def node939Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,1,0,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,3,2,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node939Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node939Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,11,10,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,5,4,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node939Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node939Generator0 else (if j.val < 2 then node939Generator1 else node939Generator2))

def node940Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,8,9,11,10,13,12,15,14,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,0,1,3,2,4,5,7,6,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node940Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,8,9,11,10,12,13,14,15,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,2,3,1,0,4,5,7,6,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node940Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,8,9,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node940Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node940Generator0 else (if j.val < 2 then node940Generator1 else node940Generator2))

def node941Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,1,0,2,3,14,15,13,12,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,15,14,12,13,2,3,0,1,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node941Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,9,8,11,10,6,7,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,11,10,8,9,5,4,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node941Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node941Generator0 else node941Generator1)

def node942Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,12,13,15,14,2,3,1,0,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,0,1,3,2,12,13,14,15,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node942Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,3,2,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,2,3,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node942Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node942Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node942Generator0 else (if j.val < 2 then node942Generator1 else node942Generator2))

def node943Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,7,6,4,5,11,10,8,9,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,6,7,5,4,10,11,9,8,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node943Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,0,1,2,3,14,15,12,13,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,13,12,15,14,1,0,2,3,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node943Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,9,8,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,11,10,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node943Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node943Generator0 else (if j.val < 2 then node943Generator1 else node943Generator2))

def node944Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,0,1,2,3,15,14,12,13,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,15,14,13,12,0,1,2,3,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node944Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,5,4,7,6,9,8,10,11,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,5,4,7,6,9,8,10,11,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node944Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node944Generator0 else node944Generator1)

def node945Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node945Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node945Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,3,2,0,1,15,14,13,12,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,15,14,12,13,2,3,0,1,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node945Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node945Generator0 else (if j.val < 2 then node945Generator1 else node945Generator2))

def node946Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,7,6,5,4,11,10,9,8,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,7,6,5,4,11,10,9,8,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node946Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,15,14,13,12,1,0,3,2,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,0,1,3,2,14,15,13,12,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node946Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node946Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node946Generator0 else (if j.val < 2 then node946Generator1 else node946Generator2))

def node947Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,3,2,0,1,14,15,12,13,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,15,14,12,13,3,2,1,0,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node947Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,6,7,4,5,10,11,8,9,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,6,7,4,5,10,11,8,9,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node947Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node947Generator0 else node947Generator1)

def node948Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node948Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5,10,11,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node948Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node948Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node948Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node948Generator0 else node948Generator1) else (if j.val < 3 then node948Generator2 else node948Generator3))

def node949Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,8,9,11,10,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,9,8,4,5,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node949Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,10,11,7,6,4,5,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,10,11,9,8,5,4,6,7,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node949Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,1,0,3,2,12,13,15,14,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,14,15,13,12,3,2,1,0,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node949Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node949Generator0 else (if j.val < 2 then node949Generator1 else node949Generator2))

def node950Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,5,4,7,6,8,9,10,11,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,5,4,7,6,8,9,10,11,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node950Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,12,13,14,15,2,3,1,0,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,3,2,0,1,13,12,15,14,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node950Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,15,14,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node950Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node950Generator0 else (if j.val < 2 then node950Generator1 else node950Generator2))

def node951Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node951Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node951Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node951Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node951Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node951Generator0 else node951Generator1) else (if j.val < 3 then node951Generator2 else node951Generator3))

def node952Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,14,15,12,13,0,1,2,3,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,1,0,3,2,14,15,13,12,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node952Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,10,11,8,9,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,10,11,8,9,6,7,4,5,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node952Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node952Generator0 else node952Generator1)

def node953Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,12,13,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node953Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,6,7,5,4,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,7,6,4,5,11,10,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node953Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,8,9,11,10,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node953Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node953Generator0 else (if j.val < 2 then node953Generator1 else node953Generator2))

def node954Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,13,12,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node954Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,5,4,7,6,10,11,8,9,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,5,4,7,6,10,11,8,9,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node954Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node954Generator0 else node954Generator1)

def node955Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,13,12,14,15,3,2,1,0,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,3,2,1,0,12,13,15,14,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node955Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,7,6,4,5,11,10,8,9,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,6,7,5,4,10,11,9,8,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node955Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node955Generator0 else node955Generator1)

def node956Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,14,15,13,12,2,3,0,1,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,2,3,0,1,14,15,13,12,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node956Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node956Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,0,1,3,2,14,15,12,13,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,14,15,12,13,0,1,3,2,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node956Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node956Generator0 else (if j.val < 2 then node956Generator1 else node956Generator2))

def node957Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,14,15,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node957Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,4,5,7,6,9,8,10,11,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,4,5,7,6,9,8,10,11,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node957Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node957Generator0 else node957Generator1)

def node958Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,3,2,5,4,14,15,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,7,6,0,1,11,10,12,13,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node958Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,11,10,9,8,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,13,12,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node958Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node958Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node958Generator0 else (if j.val < 2 then node958Generator1 else node958Generator2))

def node959Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,6,7,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,14,15,8,9,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node959Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node959Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,4,5,3,2,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,7,6,4,5,3,2,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node959Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node959Generator0 else (if j.val < 2 then node959Generator1 else node959Generator2))

def node960Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,8,9,6,7,5,4,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,11,10,8,9,6,7,5,4,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node960Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,14,15,13,12,0,1,2,3,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,2,3,0,1,13,12,14,15,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node960Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node960Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node960Generator0 else (if j.val < 2 then node960Generator1 else node960Generator2))

def node961Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node961Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,11,10,9,8,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,11,10,9,8,7,6,5,4,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node961Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node961Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node961Generator0 else (if j.val < 2 then node961Generator1 else node961Generator2))

def node962Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node962Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,0,1,3,2,6,7,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,11,10,8,9,14,15,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node962Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,11,10,9,8,15,14,13,12,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,1,0,3,2,7,6,5,4,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node962Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node962Generator0 else (if j.val < 2 then node962Generator1 else node962Generator2))

def node963Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,9,8,10,11,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,8,9,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node963Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,0,1,2,3,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,0,1,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node963Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node963Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node963Generator0 else (if j.val < 2 then node963Generator1 else node963Generator2))

def node964Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,10,11,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,10,11,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node964Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,13,12,4,5,7,6,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,11,10,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node964Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,11,10,8,9,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node964Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node964Generator0 else (if j.val < 2 then node964Generator1 else node964Generator2))

def node965Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node965Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,4,5,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node965Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,13,12,14,15,2,3,0,1,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,2,3,0,1,12,13,15,14,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node965Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node965Generator0 else (if j.val < 2 then node965Generator1 else node965Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
