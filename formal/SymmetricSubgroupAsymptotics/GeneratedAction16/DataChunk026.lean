import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
832 through 863. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node966Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,1,0,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,0,1,3,2,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node966Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node966Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,8,9,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,10,11,6,7,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node966Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node966Generator0 else (if j.val < 2 then node966Generator1 else node966Generator2))

def node967Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,1,0,7,6,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,1,0,7,6,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node967Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,14,15,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node967Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,4,5,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node967Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node967Generator0 else (if j.val < 2 then node967Generator1 else node967Generator2))

def node968Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,1,0,10,11,12,13,15,14,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,3,2,5,4,14,15,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node968Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node968Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,0,1,3,2,5,4,14,15,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,5,4,7,6,1,0,11,10,13,12,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node968Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node968Generator0 else (if j.val < 2 then node968Generator1 else node968Generator2))

def node969Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node969Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,12,13,7,6,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,9,8,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node969Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,14,15,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node969Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node969Generator0 else (if j.val < 2 then node969Generator1 else node969Generator2))

def node970Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node970Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,11,10,4,5,6,7,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,8,9,10,11,5,4,7,6,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node970Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node970Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node970Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node970Generator0 else node970Generator1) else (if j.val < 3 then node970Generator2 else node970Generator3))

def node971Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,0,1,3,2,14,15,12,13,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,15,14,13,12,1,0,2,3,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node971Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,3,2,1,0,15,14,12,13,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,13,12,14,15,1,0,3,2,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node971Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,6,7,4,5,9,8,11,10,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,6,7,4,5,9,8,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node971Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node971Generator0 else (if j.val < 2 then node971Generator1 else node971Generator2))

def node972Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node972Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,1,0,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,1,0,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node972Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node972Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node972Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node972Generator0 else node972Generator1) else (if j.val < 3 then node972Generator2 else node972Generator3))

def node973Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,1,0,2,3,14,15,12,13,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,14,15,12,13,0,1,3,2,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node973Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node973Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,8,9,10,11,4,5,6,7,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,8,9,10,11,4,5,6,7,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node973Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node973Generator0 else (if j.val < 2 then node973Generator1 else node973Generator2))

def node974Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,8,9,11,10,6,7,4,5,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,10,11,8,9,4,5,7,6,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node974Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node974Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,12,13,14,15,2,3,0,1,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,2,3,1,0,12,13,15,14,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node974Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node974Generator0 else (if j.val < 2 then node974Generator1 else node974Generator2))

def node975Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node975Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,13,12,14,15,11,10,9,8,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,12,13,15,14,11,10,9,8,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node975Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,8,9,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,10,11,6,7,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node975Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node975Generator0 else (if j.val < 2 then node975Generator1 else node975Generator2))

def node976Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,9,8,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,10,11,9,8,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node976Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node976Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,11,10,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,4,5,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node976Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node976Generator0 else (if j.val < 2 then node976Generator1 else node976Generator2))

def node977Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,0,1,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node977Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node977Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,10,11,8,9,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node977Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node977Generator0 else (if j.val < 2 then node977Generator1 else node977Generator2))

def node978Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node978Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,11,10,5,4,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,11,10,4,5,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node978Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,10,11,9,8,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,9,8,7,6,4,5,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node978Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node978Generator0 else (if j.val < 2 then node978Generator1 else node978Generator2))

def node979Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node979Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,11,10,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node979Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,9,8,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,10,11,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node979Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node979Generator0 else (if j.val < 2 then node979Generator1 else node979Generator2))

def node980Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,0,1,2,3,12,13,15,14,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,15,14,12,13,3,2,1,0,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node980Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,12,13,14,15,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,15,14,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node980Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node980Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node980Generator0 else (if j.val < 2 then node980Generator1 else node980Generator2))

def node981Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,14,15,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,14,15,2,3,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node981Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,3,2,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,2,3,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node981Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node981Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node981Generator0 else (if j.val < 2 then node981Generator1 else node981Generator2))

def node982Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,15,14,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node982Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,8,9,11,10,4,5,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,8,9,10,11,4,5,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node982Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node982Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node982Generator0 else (if j.val < 2 then node982Generator1 else node982Generator2))

def node983Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,1,0,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,0,1,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node983Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,12,13,14,15,2,3,1,0,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,1,0,2,3,14,15,12,13,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node983Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,13,12,3,2,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,15,14,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node983Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node983Generator0 else (if j.val < 2 then node983Generator1 else node983Generator2))

def node984Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,8,9,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node984Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node984Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,14,15,5,4,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,9,8,15,14,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node984Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node984Generator0 else (if j.val < 2 then node984Generator1 else node984Generator2))

def node985Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,4,5,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,15,14,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node985Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,8,9,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node985Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node985Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node985Generator0 else (if j.val < 2 then node985Generator1 else node985Generator2))

def node986Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node986Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node986Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,3,2,0,1,12,13,15,14,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,15,14,12,13,0,1,3,2,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node986Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node986Generator0 else (if j.val < 2 then node986Generator1 else node986Generator2))

def node987Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node987Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node987Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node987Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node987Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node987Generator0 else node987Generator1) else (if j.val < 3 then node987Generator2 else node987Generator3))

def node988Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,8,9,10,11,4,5,6,7,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,10,11,4,5,6,7,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node988Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,12,13,14,15,3,2,1,0,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,3,2,1,0,13,12,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node988Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,15,14,13,12,0,1,2,3,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,0,1,2,3,14,15,13,12,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node988Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node988Generator0 else (if j.val < 2 then node988Generator1 else node988Generator2))

def node989Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,11,10,8,9,12,13,14,15,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,1,0,3,2,6,7,5,4,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node989Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,13,12,14,15,9,8,10,11,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,12,13,15,14,9,8,10,11,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node989Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,14,15,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node989Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node989Generator0 else (if j.val < 2 then node989Generator1 else node989Generator2))

def node990Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,1,0,2,3,6,7,4,5,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,10,11,8,9,15,14,12,13,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node990Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,6,7,1,0,3,2,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,5,4,6,7,1,0,3,2,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node990Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node990Generator0 else node990Generator1)

def node991Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,8,9,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,10,11,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node991Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,9,8,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,10,11,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node991Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,1,0,15,14,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,2,3,0,1,15,14,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node991Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node991Generator0 else (if j.val < 2 then node991Generator1 else node991Generator2))

def node992Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,7,6,4,5,2,3,1,0,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,6,7,5,4,3,2,0,1,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node992Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,11,10,9,8,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node992Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node992Generator0 else node992Generator1)

def node993Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node993Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,13,12,15,14,11,10,9,8,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,13,12,15,14,11,10,9,8,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node993Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,9,8,5,4,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,10,11,7,6,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node993Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node993Generator0 else (if j.val < 2 then node993Generator1 else node993Generator2))

def node994Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,8,9,5,4,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,14,15,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node994Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node994Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,8,9,15,14,0,1,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,11,10,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node994Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node994Generator0 else (if j.val < 2 then node994Generator1 else node994Generator2))

def node995Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,4,5,6,7,2,3,0,1,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,4,5,6,7,3,2,1,0,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node995Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,1,0,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,2,3,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node995Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,8,9,10,11,12,13,15,14,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,0,1,2,3,4,5,6,7,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node995Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node995Generator0 else (if j.val < 2 then node995Generator1 else node995Generator2))

def node996Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,14,15,3,2,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,15,14,3,2,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node996Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node996Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,1,0,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,0,1,2,3,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node996Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node996Generator0 else (if j.val < 2 then node996Generator1 else node996Generator2))

def node997Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node997Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,14,15,13,12,1,0,2,3,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,0,1,2,3,15,14,13,12,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node997Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,9,8,10,11,7,6,5,4,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,11,10,9,8,5,4,6,7,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node997Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node997Generator0 else (if j.val < 2 then node997Generator1 else node997Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
