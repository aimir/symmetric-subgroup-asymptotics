import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
128 through 159. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node139Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,13,12,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node139Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,13,12,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,15,14,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node139Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node139Generator0 else node139Generator1)

def node140Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node140Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,8,9,11,10,14,15,13,12,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,0,1,2,3,4,5,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node140Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node140Generator0 else node140Generator1)

def node141Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,6,7,8,9,10,11,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,3,2,4,5,6,7,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node141Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,5,4,14,15,0,1,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,5,4,14,15,0,1,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node141Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,3,2,9,8,14,15,5,4,11,10,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,3,2,9,8,14,15,5,4,11,10,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node141Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node141Generator0 else (if j.val < 2 then node141Generator1 else node141Generator2))

def node142Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,7,6,8,9,11,10,13,12,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,3,2,5,4,6,7,9,8,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node142Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,5,4,14,15,0,1,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,5,4,14,15,0,1,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node142Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,2,3,9,8,15,14,5,4,10,11,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,2,3,9,8,15,14,5,4,10,11,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node142Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node142Generator0 else (if j.val < 2 then node142Generator1 else node142Generator2))

def node143Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,0,1,9,8,10,11,13,12,6,7,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,1,0,12,13,7,6,8,9,11,10,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node143Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,7,6,5,4,2,3,0,1,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,7,6,5,4,2,3,0,1,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node143Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node143Generator0 else node143Generator1)

def node144Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,5,4,3,2,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,5,4,3,2,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node144Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,9,8,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,10,11,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node144Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node144Generator0 else node144Generator1)

def node145Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,10,11,14,15,1,0,3,2,5,4,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,0,1,15,14,4,5,2,3,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node145Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,11,10,3,2,4,5,14,15,0,1,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,7,6,8,9,0,1,14,15,5,4,2,3,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node145Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,9,8,14,15,0,1,3,2,4,5,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,2,3,5,4,14,15,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node145Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node145Generator0 else (if j.val < 2 then node145Generator1 else node145Generator2))

def node146Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,3,2,4,5,15,14,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,7,6,8,9,14,15,0,1,2,3,5,4,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node146Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,0,1,15,14,4,5,2,3,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,12,13,10,11,14,15,1,0,3,2,5,4,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node146Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,8,9,3,2,5,4,15,14,0,1,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,7,6,9,8,2,3,4,5,14,15,1,0,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node146Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node146Generator0 else (if j.val < 2 then node146Generator1 else node146Generator2))

def node147Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,9,8,14,15,0,1,3,2,4,5,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,2,3,5,4,15,14,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node147Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,12,13,10,11,14,15,1,0,2,3,4,5,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,1,0,14,15,4,5,2,3,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node147Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,14,15,10,11,12,13,7,6,9,8,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,15,14,11,10,13,12,6,7,8,9,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node147Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node147Generator0 else (if j.val < 2 then node147Generator1 else node147Generator2))

def node148Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,1,0,2,3,10,11,9,8,7,6,12,13,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,15,14,11,10,9,8,6,7,12,13,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node148Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,7,6,0,1,14,15,4,5,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,12,13,10,11,5,4,2,3,1,0,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node148Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node148Generator0 else node148Generator1)

def node149Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,12,13,11,10,14,15,1,0,2,3,5,4,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,1,0,14,15,5,4,2,3,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node149Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,1,0,2,3,10,11,9,8,6,7,13,12,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,15,14,10,11,9,8,6,7,13,12,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node149Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,14,15,5,4,7,6,12,13,11,10,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,14,15,5,4,7,6,12,13,11,10,8,9,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node149Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node149Generator0 else (if j.val < 2 then node149Generator1 else node149Generator2))

def node150Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,6,7,0,1,2,3,4,5,14,15,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,8,9,10,11,4,5,14,15,0,1,2,3,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node150Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,1,0,15,14,5,4,3,2,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,13,12,11,10,14,15,0,1,2,3,4,5,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node150Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,10,11,0,1,14,15,4,5,2,3,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,12,13,10,11,0,1,14,15,4,5,2,3,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node150Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node150Generator0 else (if j.val < 2 then node150Generator1 else node150Generator2))

def node151Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,13,12,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,15,14,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node151Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,15,14,9,8,4,5,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,15,14,7,6,0,1,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node151Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node151Generator0 else node151Generator1)

def node152Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,7,6,8,9,11,10,12,13,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,5,4,6,7,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node152Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,4,5,14,15,0,1,10,11,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,2,3,4,5,14,15,0,1,10,11,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node152Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,3,2,8,9,15,14,4,5,11,10,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,3,2,8,9,15,14,4,5,11,10,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node152Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node152Generator0 else (if j.val < 2 then node152Generator1 else node152Generator2))

def node153Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node153Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,15,14,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node153Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node153Generator0 else node153Generator1)

def node154Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,8,9,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node154Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,0,1,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node154Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node154Generator0 else node154Generator1)

def node155Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,1,0,3,2,4,5,6,7,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,6,7,8,9,10,11,12,13,15,14,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node155Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,6,7,5,4,3,2,1,0,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,7,6,4,5,2,3,0,1,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node155Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,5,4,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,11,10,5,4,15,14,9,8,3,2,13,12,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node155Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node155Generator0 else (if j.val < 2 then node155Generator1 else node155Generator2))

def node156Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node156Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,14,15,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node156Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node156Generator0 else node156Generator1)

def node157Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,14,15,9,8,10,11,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,14,15,9,8,10,11,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node157Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,14,15,9,8,11,10,12,13,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,12,13,7,6,9,8,10,11,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node157Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node157Generator0 else node157Generator1)

def node158Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,14,15,8,9,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,14,15,8,9,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node158Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,14,15,8,9,11,10,13,12,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,3,2,12,13,6,7,9,8,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node158Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node158Generator0 else node158Generator1)

def node159Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,14,15,9,8,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,14,15,9,8,11,10,12,13,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node159Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,14,15,9,8,10,11,13,12,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,3,2,12,13,7,6,8,9,11,10,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node159Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node159Generator0 else node159Generator1)

def node160Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node160Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,12,13,15,14,10,11,9,8,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,12,13,15,14,11,10,8,9,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node160Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node160Generator0 else node160Generator1)

def node161Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,9,8,10,11,12,13,7,6,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,13,12,7,6,8,9,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node161Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,10,11,4,5,15,14,0,1,3,2,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,6,7,0,1,2,3,4,5,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node161Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node161Generator0 else node161Generator1)

def node162Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node162Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node162Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node162Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node162Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node162Generator0 else node162Generator1) else (if j.val < 3 then node162Generator2 else node162Generator3))

def node163Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,13,12,6,7,8,9,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,8,9,10,11,13,12,7,6,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node163Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,11,10,3,2,4,5,15,14,0,1,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,7,6,8,9,0,1,3,2,5,4,14,15,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node163Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node163Generator0 else node163Generator1)

def node164Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node164Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,13,12,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,12,13,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node164Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node164Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node164Generator0 else (if j.val < 2 then node164Generator1 else node164Generator2))

def node165Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node165Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,14,15,3,2,5,4,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,11,10,13,12,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node165Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node165Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node165Generator0 else (if j.val < 2 then node165Generator1 else node165Generator2))

def node166Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,13,12,7,6,9,8,11,10,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,9,8,11,10,13,12,7,6,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node166Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,6,7,12,13,0,1,2,3,4,5,14,15,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,8,9,10,11,2,3,1,0,15,14,4,5,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node166Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node166Generator0 else node166Generator1)

def node167Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,3,2,0,1,7,6,4,5,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,8,9,7,6,12,13,11,10,0,1,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node167Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,4,5,7,6,8,9,3,2,12,13,15,14,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,2,3,5,4,6,7,1,0,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node167Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node167Generator0 else node167Generator1)

def node168Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,4,5,10,11,8,9,15,14,12,13,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,14,15,4,5,3,2,8,9,6,7,12,13,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node168Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,0,1,7,6,4,5,2,3,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,8,9,6,7,5,4,10,11,0,1,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node168Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node168Generator0 else node168Generator1)

def node169Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,7,6,13,12,2,3,1,0,15,14,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,5,4,3,2,0,1,7,6,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node169Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,15,14,8,9,10,11,13,12,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,3,2,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node169Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node169Generator0 else node169Generator1)

def node170Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,14,15,9,8,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,14,15,9,8,11,10,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node170Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,9,8,10,11,12,13,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,2,3,13,12,7,6,8,9,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node170Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node170Generator0 else node170Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
