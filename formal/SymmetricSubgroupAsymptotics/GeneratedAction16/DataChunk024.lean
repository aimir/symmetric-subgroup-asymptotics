import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
768 through 799. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node902Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node902Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,0,1,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,2,3,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node902Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,0,1,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,2,3,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node902Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,7,6,3,2,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,5,4,7,6,1,0,3,2,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node902Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,15,14,0,1,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,15,14,12,13,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node902Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node902Generator0 else node902Generator1) else (if j.val < 3 then node902Generator2 else (if j.val < 4 then node902Generator3 else node902Generator4)))

def node903Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,2,3,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,3,2,0,1,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node903Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,8,9,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,10,11,8,9,6,7,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node903Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,5,4,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node903Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node903Generator0 else (if j.val < 2 then node903Generator1 else node903Generator2))

def node904Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,11,10,8,9,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node904Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,7,6,9,8,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,7,6,9,8,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node904Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node904Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node904Generator0 else (if j.val < 2 then node904Generator1 else node904Generator2))

def node905Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node905Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,7,6,8,9,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node905Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node905Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node905Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node905Generator0 else node905Generator1) else (if j.val < 3 then node905Generator2 else node905Generator3))

def node906Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node906Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,14,15,12,13,1,0,3,2,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,2,3,0,1,13,12,15,14,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node906Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node906Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node906Generator0 else (if j.val < 2 then node906Generator1 else node906Generator2))

def node907Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node907Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node907Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,15,14,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,12,13,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node907Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,4,5,6,7,9,8,11,10,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,4,5,6,7,9,8,11,10,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node907Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node907Generator0 else node907Generator1) else (if j.val < 3 then node907Generator2 else node907Generator3))

def node908Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node908Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node908Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node908Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,4,5,7,6,3,2,0,1,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,7,6,3,2,0,1,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node908Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,13,12,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node908Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node908Generator0 else node908Generator1) else (if j.val < 3 then node908Generator2 else (if j.val < 4 then node908Generator3 else node908Generator4)))

def node909Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node909Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,15,14,12,13,8,9,10,11,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,12,13,14,15,8,9,10,11,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node909Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node909Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,10,11,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,8,9,5,4,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node909Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node909Generator0 else node909Generator1) else (if j.val < 3 then node909Generator2 else node909Generator3))

def node910Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,5,4,6,7,8,9,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,5,4,6,7,8,9,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node910Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node910Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,8,9,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node910Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node910Generator0 else (if j.val < 2 then node910Generator1 else node910Generator2))

def node911Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,9,8,11,10,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,1,0,2,3,5,4,7,6,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node911Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,6,7,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node911Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,1,0,2,3,7,6,5,4,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,11,10,9,8,12,13,14,15,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node911Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node911Generator0 else (if j.val < 2 then node911Generator1 else node911Generator2))

def node912Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,13,12,15,14,0,1,3,2,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,2,3,1,0,13,12,15,14,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node912Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,7,6,5,4,9,8,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,7,6,5,4,9,8,11,10,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node912Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,8,9,10,11,4,5,6,7,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,8,9,10,11,4,5,6,7,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node912Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node912Generator0 else (if j.val < 2 then node912Generator1 else node912Generator2))

def node913Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,8,9,6,7,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,8,9,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node913Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,9,8,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,9,8,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node913Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node913Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node913Generator0 else (if j.val < 2 then node913Generator1 else node913Generator2))

def node914Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,11,10,8,9,6,7,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,11,10,8,9,6,7,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node914Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,0,1,2,3,15,14,12,13,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,14,15,12,13,2,3,1,0,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node914Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node914Generator0 else node914Generator1)

def node915Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,8,9,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,9,8,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node915Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,9,8,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node915Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node915Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node915Generator0 else (if j.val < 2 then node915Generator1 else node915Generator2))

def node916Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node916Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node916Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,3,2,13,12,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,2,3,12,13,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node916Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node916Generator0 else (if j.val < 2 then node916Generator1 else node916Generator2))

def node917Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,10,11,8,9,12,13,15,14,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,3,2,0,1,6,7,4,5,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node917Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,1,0,2,3,6,7,4,5,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,10,11,8,9,15,14,12,13,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node917Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node917Generator0 else node917Generator1)

def node918Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node918Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,13,12,5,4,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,10,11,1,0,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node918Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node918Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node918Generator0 else (if j.val < 2 then node918Generator1 else node918Generator2))

def node919Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node919Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node919Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node919Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node919Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node919Generator0 else node919Generator1) else (if j.val < 3 then node919Generator2 else node919Generator3))

def node920Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node920Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,10,11,6,7,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,8,9,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node920Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,8,9,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node920Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node920Generator0 else (if j.val < 2 then node920Generator1 else node920Generator2))

def node921Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node921Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,15,14,5,4,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,10,11,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node921Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,10,11,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,9,8,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node921Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node921Generator0 else (if j.val < 2 then node921Generator1 else node921Generator2))

def node922Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,0,1,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,0,1,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node922Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node922Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,6,7,8,9,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,6,7,8,9,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node922Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node922Generator0 else (if j.val < 2 then node922Generator1 else node922Generator2))

def node923Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,9,8,1,0,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,12,13,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node923Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node923Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node923Generator0 else node923Generator1)

def node924Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node924Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,10,11,9,8,5,4,6,7,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,9,8,10,11,7,6,4,5,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node924Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node924Generator0 else node924Generator1)

def node925Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,11,10,9,8,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,3,2,0,1,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node925Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,1,0,2,3,4,5,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,8,9,10,11,12,13,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node925Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,14,15,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node925Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node925Generator0 else (if j.val < 2 then node925Generator1 else node925Generator2))

def node926Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,11,10,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,10,11,4,5,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node926Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,15,14,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,14,15,3,2,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node926Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,10,11,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node926Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node926Generator0 else (if j.val < 2 then node926Generator1 else node926Generator2))

def node927Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,11,10,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,8,9,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node927Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,15,14,12,13,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,1,0,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node927Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node927Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node927Generator0 else (if j.val < 2 then node927Generator1 else node927Generator2))

def node928Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node928Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,5,4,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,4,5,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node928Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,5,4,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,10,11,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node928Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node928Generator0 else (if j.val < 2 then node928Generator1 else node928Generator2))

def node929Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,5,4,7,6,10,11,9,8,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,5,4,7,6,11,10,8,9,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node929Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,2,3,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node929Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node929Generator0 else node929Generator1)

def node930Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node930Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,8,9,6,7,5,4,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,11,10,8,9,6,7,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node930Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node930Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node930Generator0 else (if j.val < 2 then node930Generator1 else node930Generator2))

def node931Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node931Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node931Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,4,5,7,6,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,4,5,7,6,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node931Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node931Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node931Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node931Generator0 else node931Generator1) else (if j.val < 3 then node931Generator2 else (if j.val < 4 then node931Generator3 else node931Generator4)))

def node932Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,14,15,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node932Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node932Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node932Generator0 else node932Generator1)

def node933Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,13,12,14,15,1,0,3,2,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,1,0,3,2,12,13,15,14,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node933Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node933Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,8,9,7,6,4,5,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,10,11,9,8,6,7,5,4,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node933Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node933Generator0 else (if j.val < 2 then node933Generator1 else node933Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
