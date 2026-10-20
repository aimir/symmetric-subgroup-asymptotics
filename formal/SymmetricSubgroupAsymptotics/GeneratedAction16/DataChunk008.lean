import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
256 through 287. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node286Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,9,8,10,11,13,12,14,15,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,2,3,0,1,5,4,6,7,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node286Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,1,0,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node286Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node286Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node286Generator0 else (if j.val < 2 then node286Generator1 else node286Generator2))

def node287Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,10,11,9,8,6,7,5,4,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,11,10,8,9,7,6,4,5,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node287Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node287Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,3,2,0,1,12,13,15,14,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,12,13,15,14,2,3,1,0,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node287Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node287Generator0 else (if j.val < 2 then node287Generator1 else node287Generator2))

def node288Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node288Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node288Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node288Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,12,13,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node288Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node288Generator0 else node288Generator1) else (if j.val < 3 then node288Generator2 else node288Generator3))

def node289Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,14,15,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,10,11,13,12,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node289Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,13,12,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,8,9,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node289Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node289Generator0 else node289Generator1)

def node290Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,1,0,2,3,6,7,5,4,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,11,10,8,9,14,15,12,13,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node290Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,11,10,9,8,12,13,14,15,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,2,3,1,0,7,6,5,4,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node290Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node290Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node290Generator0 else (if j.val < 2 then node290Generator1 else node290Generator2))

def node291Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,2,3,1,0,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node291Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,11,10,5,4,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,10,11,4,5,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node291Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,13,12,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node291Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node291Generator0 else (if j.val < 2 then node291Generator1 else node291Generator2))

def node292Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node292Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,12,13,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,9,8,11,10,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node292Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,13,12,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,11,10,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node292Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node292Generator0 else (if j.val < 2 then node292Generator1 else node292Generator2))

def node293Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,12,13,14,15,2,3,0,1,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,2,3,0,1,12,13,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node293Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,8,9,7,6,4,5,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,10,11,9,8,6,7,5,4,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node293Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,15,14,12,13,0,1,3,2,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,1,0,2,3,14,15,13,12,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node293Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node293Generator0 else (if j.val < 2 then node293Generator1 else node293Generator2))

def node294Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node294Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node294Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,9,8,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node294Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node294Generator0 else (if j.val < 2 then node294Generator1 else node294Generator2))

def node295Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node295Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node295Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,7,6,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,9,8,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node295Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node295Generator0 else (if j.val < 2 then node295Generator1 else node295Generator2))

def node296Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node296Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,4,5,2,3,6,7,11,10,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,4,5,2,3,6,7,11,10,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node296Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node296Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node296Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,15,14,5,4,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,9,8,14,15,4,5,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node296Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node296Generator0 else node296Generator1) else (if j.val < 3 then node296Generator2 else (if j.val < 4 then node296Generator3 else node296Generator4)))

def node297Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node297Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,12,13,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,9,8,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node297Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,3,2,4,5,8,9,15,14,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,6,7,0,1,8,9,14,15,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node297Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node297Generator0 else (if j.val < 2 then node297Generator1 else node297Generator2))

def node298Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node298Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,9,8,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,10,11,9,8,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node298Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,11,10,4,5,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,8,9,11,10,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node298Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node298Generator0 else (if j.val < 2 then node298Generator1 else node298Generator2))

def node299Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,11,10,8,9,7,6,4,5,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,10,11,9,8,6,7,5,4,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node299Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,3,2,1,0,13,12,15,14,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,13,12,15,14,3,2,1,0,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node299Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,13,12,15,14,2,3,0,1,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,3,2,1,0,12,13,14,15,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node299Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node299Generator0 else (if j.val < 2 then node299Generator1 else node299Generator2))

def node300Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,1,0,2,3,15,14,12,13,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,14,15,13,12,1,0,2,3,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node300Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,14,15,13,12,0,1,3,2,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,0,1,3,2,15,14,12,13,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node300Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node300Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node300Generator0 else (if j.val < 2 then node300Generator1 else node300Generator2))

def node301Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node301Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node301Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node301Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node301Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node301Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node301Generator0 else node301Generator1) else (if j.val < 3 then node301Generator2 else (if j.val < 4 then node301Generator3 else node301Generator4)))

def node302Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,11,10,1,0,6,7,13,12,3,2,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,11,10,1,0,6,7,13,12,3,2,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node302Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,12,13,15,14,9,8,11,10,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,10,11,13,12,7,6,9,8,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node302Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,11,10,8,9,15,14,13,12,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,1,0,15,14,4,5,3,2,9,8,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node302Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node302Generator0 else (if j.val < 2 then node302Generator1 else node302Generator2))

def node303Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node303Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,4,5,6,7,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,4,5,6,7,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node303Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node303Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node303Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node303Generator0 else node303Generator1) else (if j.val < 3 then node303Generator2 else node303Generator3))

def node304Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node304Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,15,14,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node304Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,8,9,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,8,9,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node304Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node304Generator0 else (if j.val < 2 then node304Generator1 else node304Generator2))

def node305Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,8,9,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,8,9,10,11,6,7,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node305Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node305Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node305Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node305Generator0 else (if j.val < 2 then node305Generator1 else node305Generator2))

def node306Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,11,10,9,8,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node306Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node306Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node306Generator0 else node306Generator1)

def node307Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,13,12,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,15,14,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node307Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node307Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,11,10,9,8,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node307Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node307Generator0 else (if j.val < 2 then node307Generator1 else node307Generator2))

def node308Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node308Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node308Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node308Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,2,3,5,4,1,0,11,10,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,2,3,5,4,1,0,11,10,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node308Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,10,11,1,0,7,6,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,13,12,11,10,0,1,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node308Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node308Generator0 else node308Generator1) else (if j.val < 3 then node308Generator2 else (if j.val < 4 then node308Generator3 else node308Generator4)))

def node309Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node309Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node309Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,13,12,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node309Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node309Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node309Generator0 else node309Generator1) else (if j.val < 3 then node309Generator2 else node309Generator3))

def node310Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,9,8,11,10,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node310Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,0,1,14,15,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,0,1,14,15,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node310Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,1,0,14,15,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,1,0,14,15,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node310Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node310Generator0 else (if j.val < 2 then node310Generator1 else node310Generator2))

def node311Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node311Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,13,12,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node311Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node311Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node311Generator0 else (if j.val < 2 then node311Generator1 else node311Generator2))

def node312Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node312Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,6,7,4,5,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,6,7,4,5,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node312Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node312Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node312Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node312Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node312Generator0 else node312Generator1) else (if j.val < 3 then node312Generator2 else (if j.val < 4 then node312Generator3 else node312Generator4)))

def node313Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node313Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node313Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node313Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node313Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node313Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node313Generator0 else node313Generator1) else (if j.val < 3 then node313Generator2 else (if j.val < 4 then node313Generator3 else node313Generator4)))

def node314Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node314Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,0,1,2,3,7,6,5,4,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,11,10,9,8,14,15,13,12,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node314Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node314Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node314Generator0 else (if j.val < 2 then node314Generator1 else node314Generator2))

def node315Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,13,12,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node315Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,15,14,6,7,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,11,10,8,9,2,3,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node315Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,14,15,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,9,8,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node315Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node315Generator0 else (if j.val < 2 then node315Generator1 else node315Generator2))

def node316Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,9,8,6,7,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,11,10,8,9,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node316Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node316Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node316Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node316Generator0 else (if j.val < 2 then node316Generator1 else node316Generator2))

def node317Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node317Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node317Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,8,9,10,11,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,12,13,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node317Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node317Generator0 else (if j.val < 2 then node317Generator1 else node317Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
