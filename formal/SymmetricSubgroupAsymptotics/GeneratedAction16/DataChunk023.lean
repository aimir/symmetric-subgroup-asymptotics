import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
736 through 767. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node870Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node870Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,8,9,11,10,4,5,7,6,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node870Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,5,4,6,7,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,5,4,6,7,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node870Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node870Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node870Generator0 else node870Generator1) else (if j.val < 3 then node870Generator2 else node870Generator3))

def node871Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,1,0,3,2,14,15,12,13,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,13,12,15,14,2,3,0,1,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node871Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,4,5,7,6,10,11,8,9,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,4,5,7,6,10,11,8,9,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node871Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,10,11,9,8,6,7,5,4,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,11,10,8,9,7,6,4,5,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node871Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node871Generator0 else (if j.val < 2 then node871Generator1 else node871Generator2))

def node872Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,13,12,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node872Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,1,0,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,0,1,2,3,9,8,11,10,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node872Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node872Generator0 else node872Generator1)

def node873Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,7,6,4,5,8,9,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,5,4,8,9,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node873Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,11,10,9,8,6,7,4,5,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,10,11,8,9,7,6,5,4,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node873Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,13,12,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,15,14,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node873Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node873Generator0 else (if j.val < 2 then node873Generator1 else node873Generator2))

def node874Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,9,8,2,3,0,1,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,13,12,15,14,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node874Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,11,10,9,8,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,9,8,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node874Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,10,11,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node874Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node874Generator0 else (if j.val < 2 then node874Generator1 else node874Generator2))

def node875Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,10,11,9,8,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,7,6,4,5,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node875Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,11,10,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,11,10,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node875Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node875Generator0 else node875Generator1)

def node876Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node876Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,12,13,1,0,6,7,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,10,11,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node876Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,3,2,5,4,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,7,6,1,0,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node876Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node876Generator0 else (if j.val < 2 then node876Generator1 else node876Generator2))

def node877Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node877Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node877Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node877Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,4,5,6,7,3,2,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,6,7,2,3,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node877Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,13,12,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node877Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node877Generator0 else node877Generator1) else (if j.val < 3 then node877Generator2 else (if j.val < 4 then node877Generator3 else node877Generator4)))

def node878Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node878Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node878Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node878Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,9,8,15,14,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,5,4,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node878Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node878Generator0 else node878Generator1) else (if j.val < 3 then node878Generator2 else node878Generator3))

def node879Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node879Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node879Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node879Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,4,5,7,6,3,2,0,1,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,4,5,7,6,3,2,0,1,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node879Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,13,12,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node879Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node879Generator0 else node879Generator1) else (if j.val < 3 then node879Generator2 else (if j.val < 4 then node879Generator3 else node879Generator4)))

def node880Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node880Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node880Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node880Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node880Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node880Generator0 else node880Generator1) else (if j.val < 3 then node880Generator2 else node880Generator3))

def node881Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,9,8,11,10,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,8,9,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node881Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,2,3,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,12,13,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node881Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,8,9,11,10,6,7,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,8,9,4,5,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node881Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node881Generator0 else (if j.val < 2 then node881Generator1 else node881Generator2))

def node882Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,7,6,4,5,10,11,9,8,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,6,7,5,4,11,10,8,9,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node882Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,13,12,14,15,3,2,0,1,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,3,2,1,0,12,13,14,15,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node882Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,15,14,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node882Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node882Generator0 else (if j.val < 2 then node882Generator1 else node882Generator2))

def node883Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,11,10,8,9,14,15,12,13,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,0,1,2,3,6,7,5,4,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node883Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node883Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node883Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node883Generator0 else (if j.val < 2 then node883Generator1 else node883Generator2))

def node884Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,3,2,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node884Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,6,7,5,4,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,7,6,4,5,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node884Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,9,8,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,10,11,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node884Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node884Generator0 else (if j.val < 2 then node884Generator1 else node884Generator2))

def node885Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,5,4,6,7,0,1,2,3,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,5,4,6,7,2,3,1,0,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node885Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,7,6,5,4,3,2,0,1,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,5,4,0,1,2,3,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node885Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,8,9,10,11,13,12,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,3,2,1,0,4,5,6,7,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node885Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node885Generator0 else (if j.val < 2 then node885Generator1 else node885Generator2))

def node886Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node886Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node886Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,0,1,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,0,1,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node886Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,13,12,1,0,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,14,15,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node886Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,11,10,4,5,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,8,9,10,11,5,4,7,6,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node886Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node886Generator0 else node886Generator1) else (if j.val < 3 then node886Generator2 else (if j.val < 4 then node886Generator3 else node886Generator4)))

def node887Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,5,4,6,7,0,1,2,3,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,5,4,6,7,2,3,0,1,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node887Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node887Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,1,0,2,3,6,7,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,10,11,8,9,13,12,15,14,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node887Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node887Generator0 else (if j.val < 2 then node887Generator1 else node887Generator2))

def node888Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,8,9,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node888Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,7,6,4,5,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,5,4,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node888Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node888Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node888Generator0 else (if j.val < 2 then node888Generator1 else node888Generator2))

def node889Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,8,9,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node889Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,9,8,11,10,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,5,4,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node889Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,10,11,8,9,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node889Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node889Generator0 else (if j.val < 2 then node889Generator1 else node889Generator2))

def node890Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,2,3,12,13,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,2,3,1,0,14,15,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node890Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,2,3,1,0,14,15,12,13,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,14,15,13,12,3,2,1,0,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node890Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,0,1,2,3,15,14,13,12,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,14,15,13,12,1,0,2,3,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node890Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node890Generator0 else (if j.val < 2 then node890Generator1 else node890Generator2))

def node891Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,9,8,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node891Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,7,6,5,4,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,7,6,5,4,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node891Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node891Generator0 else node891Generator1)

def node892Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node892Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,2,3,0,1,6,7,4,5,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,10,11,8,9,15,14,13,12,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node892Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,14,15,13,12,8,9,10,11,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,12,13,14,15,8,9,10,11,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node892Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node892Generator0 else (if j.val < 2 then node892Generator1 else node892Generator2))

def node893Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,8,9,2,3,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,13,12,6,7,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node893Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,13,12,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,15,14,2,3,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node893Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,2,3,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node893Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node893Generator0 else (if j.val < 2 then node893Generator1 else node893Generator2))

def node894Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,6,7,5,4,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,7,6,4,5,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node894Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,8,9,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node894Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,12,13,15,14,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,15,14,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node894Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node894Generator0 else (if j.val < 2 then node894Generator1 else node894Generator2))

def node895Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node895Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node895Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,15,14,12,13,0,1,3,2,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,13,12,1,0,2,3,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node895Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node895Generator0 else (if j.val < 2 then node895Generator1 else node895Generator2))

def node896Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node896Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,6,7,4,5,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,6,7,4,5,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node896Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,3,2,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,1,0,3,2,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node896Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,3,2,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,12,13,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node896Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node896Generator0 else node896Generator1) else (if j.val < 3 then node896Generator2 else node896Generator3))

def node897Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,8,9,11,10,6,7,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,11,10,8,9,4,5,7,6,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node897Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,10,11,9,8,6,7,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,11,10,8,9,7,6,4,5,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node897Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,2,3,0,1,12,13,15,14,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,12,13,15,14,1,0,3,2,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node897Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node897Generator0 else (if j.val < 2 then node897Generator1 else node897Generator2))

def node898Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,14,15,12,13,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node898Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,14,15,12,13,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node898Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node898Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node898Generator0 else (if j.val < 2 then node898Generator1 else node898Generator2))

def node899Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,14,15,13,12,0,1,3,2,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,1,0,3,2,14,15,12,13,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node899Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,9,8,11,10,6,7,5,4,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,11,10,8,9,5,4,7,6,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node899Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,11,10,9,8,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,11,10,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node899Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node899Generator0 else (if j.val < 2 then node899Generator1 else node899Generator2))

def node900Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,10,11,8,9,12,13,14,15,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,2,3,1,0,6,7,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node900Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,11,10,9,8,13,12,15,14,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,2,3,1,0,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node900Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,11,10,7,6,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,9,8,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node900Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node900Generator0 else (if j.val < 2 then node900Generator1 else node900Generator2))

def node901Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,14,15,1,0,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,15,14,13,12,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node901Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,8,9,11,10,6,7,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,11,10,8,9,4,5,7,6,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node901Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node901Generator0 else node901Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
