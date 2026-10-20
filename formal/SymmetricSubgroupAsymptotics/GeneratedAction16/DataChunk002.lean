import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
64 through 95. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node75Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,7,6,4,5,2,3,0,1,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,7,6,4,5,2,3,0,1,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node75Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,3,2,8,9,14,15,4,5,11,10,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,3,2,8,9,14,15,4,5,11,10,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node75Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,6,7,5,4,3,2,1,0,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,7,6,4,5,2,3,0,1,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node75Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node75Generator0 else (if j.val < 2 then node75Generator1 else node75Generator2))

def node76Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,11,10,3,2,0,1,15,14,4,5,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,7,6,12,13,0,1,3,2,5,4,14,15,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node76Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,1,0,2,3,4,5,15,14,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,8,9,10,11,14,15,4,5,2,3,0,1,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node76Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,14,15,4,5,8,9,10,11,13,12,7,6,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,14,15,4,5,13,12,6,7,8,9,11,10,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node76Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node76Generator0 else (if j.val < 2 then node76Generator1 else node76Generator2))

def node77Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,5,4,3,2,0,1,7,6,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,13,12,2,3,1,0,15,14,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node77Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,8,9,2,3,12,13,6,7,0,1,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,6,7,0,1,10,11,4,5,14,15,8,9,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node77Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node77Generator0 else node77Generator1)

def node78Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,13,12,3,2,0,1,15,14,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,5,4,2,3,1,0,7,6,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node78Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,12,13,7,6,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node78Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,15,14,1,0,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node78Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node78Generator0 else (if j.val < 2 then node78Generator1 else node78Generator2))

def node79Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,6,7,3,2,4,5,15,14,1,0,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,7,6,8,9,4,5,3,2,0,1,14,15,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node79Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,2,3,12,13,11,10,9,8,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,2,3,12,13,11,10,9,8,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node79Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,10,11,5,4,2,3,1,0,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,7,6,0,1,15,14,4,5,2,3,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node79Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node79Generator0 else (if j.val < 2 then node79Generator1 else node79Generator2))

def node80Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node80Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,1,0,6,7,2,3,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,6,7,0,1,4,5,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node80Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node80Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,11,10,12,13,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,12,13,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node80Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node80Generator0 else node80Generator1) else (if j.val < 3 then node80Generator2 else node80Generator3))

def node81Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,8,9,6,7,12,13,10,11,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,8,9,6,7,12,13,10,11,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node81Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,0,1,11,10,13,12,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,1,0,10,11,12,13,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node81Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node81Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node81Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,7,6,9,8,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,7,6,9,8,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node81Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node81Generator0 else node81Generator1) else (if j.val < 3 then node81Generator2 else (if j.val < 4 then node81Generator3 else node81Generator4)))

def node82Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,8,9,6,7,13,12,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,8,9,6,7,13,12,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node82Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,0,1,11,10,13,12,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,1,0,10,11,12,13,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node82Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node82Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node82Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node82Generator0 else node82Generator1) else (if j.val < 3 then node82Generator2 else node82Generator3))

def node83Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,8,9,6,7,13,12,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,8,9,6,7,13,12,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node83Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,13,12,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node83Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node83Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node83Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node83Generator0 else node83Generator1) else (if j.val < 3 then node83Generator2 else node83Generator3))

def node84Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,13,12,14,15,9,8,11,10,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,10,11,12,13,7,6,9,8,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node84Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,2,3,5,4,15,14,1,0,10,11,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,2,3,5,4,15,14,1,0,10,11,13,12,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node84Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node84Generator0 else node84Generator1)

def node85Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,4,5,6,7,0,1,2,3,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,4,5,6,7,0,1,2,3,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node85Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,7,6,8,9,11,10,12,13,15,14,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,5,4,6,7,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node85Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node85Generator0 else node85Generator1)

def node86Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node86Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,3,2,0,1,7,6,5,4,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,11,10,9,8,12,13,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node86Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,14,15,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,14,15,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node86Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node86Generator0 else (if j.val < 2 then node86Generator1 else node86Generator2))

def node87Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,9,8,7,6,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node87Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,0,1,11,10,13,12,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,1,0,10,11,12,13,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node87Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node87Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node87Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node87Generator0 else node87Generator1) else (if j.val < 3 then node87Generator2 else node87Generator3))

def node88Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,1,0,11,10,13,12,6,7,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,0,1,10,11,12,13,7,6,9,8,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node88Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,2,3,9,8,6,7,4,5,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,10,11,8,9,7,6,12,13,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node88Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node88Generator0 else node88Generator1)

def node89Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,15,14,12,13,11,10,8,9,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,15,14,12,13,11,10,8,9,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node89Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node89Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,3,2,8,9,14,15,4,5,11,10,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,3,2,8,9,14,15,4,5,11,10,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node89Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,8,9,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node89Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node89Generator0 else node89Generator1) else (if j.val < 3 then node89Generator2 else node89Generator3))

def node90Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node90Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,12,13,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node90Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node90Generator0 else node90Generator1)

def node91Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,14,15,4,5,10,11,8,9,7,6,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,13,12,10,11,8,9,15,14,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node91Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,0,1,7,6,4,5,2,3,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,12,13,10,11,9,8,15,14,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node91Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node91Generator0 else node91Generator1)

def node92Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,12,13,10,11,8,9,14,15,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,15,14,5,4,10,11,8,9,6,7,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node92Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,10,11,12,13,7,6,9,8,2,3,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,10,11,12,13,7,6,9,8,2,3,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node92Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,7,6,9,8,3,2,5,4,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,7,6,9,8,3,2,5,4,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node92Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node92Generator0 else (if j.val < 2 then node92Generator1 else node92Generator2))

def node93Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,4,5,15,14,0,1,11,10,12,13,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,4,5,15,14,0,1,11,10,12,13,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node93Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,10,11,5,4,14,15,1,0,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,7,6,0,1,2,3,4,5,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node93Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,7,6,8,9,3,2,4,5,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,7,6,8,9,3,2,4,5,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node93Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node93Generator0 else (if j.val < 2 then node93Generator1 else node93Generator2))

def node94Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,5,4,6,7,8,9,3,2,13,12,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,3,2,4,5,6,7,0,1,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node94Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,0,1,10,11,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,1,0,2,3,5,4,14,15,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node94Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,10,11,13,12,14,15,8,9,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,12,13,14,15,0,1,10,11,4,5,7,6,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node94Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node94Generator0 else (if j.val < 2 then node94Generator1 else node94Generator2))

def node95Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,15,14,9,8,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node95Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node95Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node95Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node95Generator0 else (if j.val < 2 then node95Generator1 else node95Generator2))

def node96Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,8,9,15,14,0,1,2,3,5,4,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,2,3,4,5,15,14,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node96Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,15,14,6,7,12,13,10,11,8,9,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,3,2,6,7,12,13,10,11,8,9,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node96Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node96Generator0 else node96Generator1)

def node97Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,7,6,13,12,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node97Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,0,1,10,11,12,13,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,1,0,11,10,13,12,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node97Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node97Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,2,3,4,5,9,8,7,6,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node97Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,2,3,6,7,8,9,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node97Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node97Generator0 else node97Generator1) else (if j.val < 3 then node97Generator2 else (if j.val < 4 then node97Generator3 else node97Generator4)))

def node98Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,8,9,6,7,13,12,11,10,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,8,9,6,7,13,12,11,10,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node98Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,15,14,0,1,10,11,12,13,7,6,9,8,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,1,0,11,10,13,12,6,7,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node98Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node98Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,3,2,5,4,8,9,6,7,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node98Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node98Generator0 else node98Generator1) else (if j.val < 3 then node98Generator2 else node98Generator3))

def node99Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node99Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,9,8,10,11,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,4,5,7,6,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node99Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,5,4,7,6,0,1,2,3,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,5,4,7,6,0,1,2,3,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node99Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node99Generator0 else (if j.val < 2 then node99Generator1 else node99Generator2))

def node100Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node100Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node100Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node100Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node100Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node100Generator0 else node100Generator1) else (if j.val < 3 then node100Generator2 else node100Generator3))

def node101Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,10,11,9,8,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,10,11,9,8,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node101Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,11,10,4,5,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,8,9,10,11,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node101Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node101Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node101Generator0 else (if j.val < 2 then node101Generator1 else node101Generator2))

def node102Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,9,8,11,10,12,13,15,14,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,1,0,2,3,5,4,7,6,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node102Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,4,5,3,2,0,1,7,6,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,9,8,14,15,13,12,10,11,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node102Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,8,9,6,7,4,5,11,10,1,0,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,0,1,6,7,4,5,2,3,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node102Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node102Generator0 else (if j.val < 2 then node102Generator1 else node102Generator2))

def node103Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node103Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node103Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,14,15,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,2,3,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node103Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node103Generator0 else (if j.val < 2 then node103Generator1 else node103Generator2))

def node104Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,1,0,3,2,6,7,5,4,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,11,10,8,9,15,14,12,13,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node104Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,3,2,0,1,5,4,7,6,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,9,8,11,10,12,13,14,15,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node104Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node104Generator0 else node104Generator1)

def node105Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,9,8,7,6,12,13,10,11,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,9,8,7,6,12,13,10,11,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node105Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node105Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,0,1,6,7,8,9,10,11,12,13,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,6,7,8,9,10,11,12,13,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node105Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,14,15,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node105Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,2,3,6,7,8,9,10,11,12,13,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,4,5,2,3,6,7,8,9,10,11,12,13,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node105Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node105Generator0 else node105Generator1) else (if j.val < 3 then node105Generator2 else (if j.val < 4 then node105Generator3 else node105Generator4)))

def node106Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node106Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,9,8,10,11,6,7,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,8,9,5,4,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node106Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,10,11,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,11,10,9,8,5,4,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node106Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node106Generator0 else (if j.val < 2 then node106Generator1 else node106Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
