import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
192 through 223. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node222Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,13,12,14,15,2,3,1,0,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,3,2,0,1,13,12,14,15,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node222Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,1,0,3,2,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,3,2,1,0,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node222Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,7,6,4,5,11,10,8,9,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,6,7,5,4,10,11,9,8,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node222Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node222Generator0 else (if j.val < 2 then node222Generator1 else node222Generator2))

def node223Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node223Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node223Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,13,12,15,14,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,12,13,14,15,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node223Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,4,5,6,7,9,8,11,10,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,4,5,6,7,9,8,11,10,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node223Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node223Generator0 else node223Generator1) else (if j.val < 3 then node223Generator2 else node223Generator3))

def node224Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node224Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,3,2,0,1,12,13,15,14,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,12,13,15,14,3,2,0,1,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node224Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,6,7,5,4,11,10,8,9,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,7,6,4,5,10,11,9,8,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node224Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node224Generator0 else (if j.val < 2 then node224Generator1 else node224Generator2))

def node225Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node225Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,8,9,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,9,8,15,14,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node225Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node225Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node225Generator0 else (if j.val < 2 then node225Generator1 else node225Generator2))

def node226Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,1,0,2,3,15,14,12,13,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,14,15,13,12,1,0,2,3,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node226Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,7,6,5,4,10,11,8,9,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,7,6,5,4,10,11,8,9,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node226Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,14,15,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node226Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node226Generator0 else (if j.val < 2 then node226Generator1 else node226Generator2))

def node227Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,13,12,15,14,8,9,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,13,12,15,14,8,9,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node227Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,7,6,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node227Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,5,4,10,11,8,9,7,6,12,13,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,3,2,9,8,6,7,4,5,10,11,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node227Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node227Generator0 else (if j.val < 2 then node227Generator1 else node227Generator2))

def node228Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node228Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,6,7,8,9,2,3,4,5,14,15,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,10,11,4,5,6,7,1,0,2,3,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node228Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node228Generator0 else node228Generator1)

def node229Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node229Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,1,0,2,3,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,2,3,1,0,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node229Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,11,10,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,4,5,7,6,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node229Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node229Generator0 else (if j.val < 2 then node229Generator1 else node229Generator2))

def node230Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,9,8,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,15,14,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node230Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node230Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,8,9,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node230Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node230Generator0 else (if j.val < 2 then node230Generator1 else node230Generator2))

def node231Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node231Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,8,9,2,3,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,13,12,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node231Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,12,13,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node231Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node231Generator0 else (if j.val < 2 then node231Generator1 else node231Generator2))

def node232Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,7,6,5,4,11,10,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,7,6,5,4,11,10,9,8,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node232Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,11,10,8,9,7,6,4,5,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,10,11,9,8,6,7,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node232Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,1,0,3,2,15,14,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,2,3,1,0,13,12,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node232Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node232Generator0 else (if j.val < 2 then node232Generator1 else node232Generator2))

def node233Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,0,1,3,2,4,5,6,7,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,8,9,10,11,14,15,12,13,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node233Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,11,10,8,9,15,14,12,13,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,1,0,3,2,6,7,5,4,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node233Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,3,2,0,1,6,7,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,10,11,8,9,13,12,15,14,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node233Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node233Generator0 else (if j.val < 2 then node233Generator1 else node233Generator2))

def node234Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,13,12,14,15,2,3,1,0,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,2,3,1,0,13,12,14,15,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node234Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,5,4,6,7,8,9,11,10,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,5,4,6,7,8,9,11,10,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node234Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node234Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node234Generator0 else (if j.val < 2 then node234Generator1 else node234Generator2))

def node235Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,8,9,6,7,5,4,11,10,0,1,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,1,0,7,6,4,5,2,3,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node235Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,13,12,15,14,8,9,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,13,12,15,14,8,9,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node235Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,13,12,6,7,9,8,11,10,4,5,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,10,11,4,5,7,6,9,8,3,2,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node235Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node235Generator0 else (if j.val < 2 then node235Generator1 else node235Generator2))

def node236Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node236Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,13,12,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,14,15,2,3,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node236Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,5,4,6,7,8,9,11,10,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,5,4,6,7,8,9,11,10,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node236Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node236Generator0 else (if j.val < 2 then node236Generator1 else node236Generator2))

def node237Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node237Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,5,4,3,2,13,12,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,7,6,5,4,3,2,13,12,10,11,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node237Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,14,15,9,8,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,11,10,8,9,7,6,0,1,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node237Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node237Generator0 else (if j.val < 2 then node237Generator1 else node237Generator2))

def node238Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,10,11,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,11,10,4,5,6,7,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node238Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,11,10,9,8,6,7,4,5,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,10,11,8,9,7,6,5,4,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node238Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,14,15,13,12,0,1,3,2,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,0,1,3,2,14,15,13,12,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node238Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node238Generator0 else (if j.val < 2 then node238Generator1 else node238Generator2))

def node239Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node239Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node239Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,15,14,13,12,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,14,15,12,13,0,1,2,3,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node239Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node239Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node239Generator0 else node239Generator1) else (if j.val < 3 then node239Generator2 else node239Generator3))

def node240Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,14,15,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,12,13,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node240Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node240Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,4,5,2,3,9,8,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3,9,8,15,14,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node240Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node240Generator0 else (if j.val < 2 then node240Generator1 else node240Generator2))

def node241Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node241Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node241Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node241Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node241Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node241Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node241Generator0 else node241Generator1) else (if j.val < 3 then node241Generator2 else (if j.val < 4 then node241Generator3 else node241Generator4)))

def node242Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,7,6,4,5,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,6,7,5,4,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node242Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,0,1,2,3,5,4,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,9,8,11,10,14,15,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node242Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node242Generator0 else node242Generator1)

def node243Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,5,4,7,6,8,9,10,11,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,5,4,7,6,8,9,10,11,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node243Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,3,2,1,0,13,12,15,14,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,13,12,15,14,3,2,1,0,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node243Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node243Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node243Generator0 else (if j.val < 2 then node243Generator1 else node243Generator2))

def node244Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,0,1,3,2,14,15,13,12,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,15,14,12,13,1,0,2,3,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node244Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node244Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node244Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node244Generator0 else (if j.val < 2 then node244Generator1 else node244Generator2))

def node245Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,15,14,8,9,11,10,12,13,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,15,14,8,9,11,10,12,13,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node245Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,12,13,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,12,13,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node245Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,4,5,7,6,1,0,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,3,2,4,5,7,6,1,0,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node245Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,8,9,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,8,9,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node245Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node245Generator0 else node245Generator1) else (if j.val < 3 then node245Generator2 else node245Generator3))

def node246Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,13,12,6,7,8,9,10,11,5,4,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,13,12,6,7,8,9,10,11,5,4,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node246Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,12,13,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,15,14,0,1,11,10,12,13,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node246Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,3,2,5,4,7,6,0,1,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,5,4,7,6,0,1,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node246Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,8,9,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,8,9,6,7,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node246Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node246Generator0 else node246Generator1) else (if j.val < 3 then node246Generator2 else node246Generator3))

def node247Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,10,11,3,2,5,4,15,14,1,0,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,7,6,9,8,0,1,14,15,4,5,2,3,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node247Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,14,15,0,1,13,12,11,10,9,8,7,6,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,13,12,11,10,9,8,7,6,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node247Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,15,14,8,9,11,10,12,13,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,1,0,2,3,13,12,6,7,9,8,10,11,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node247Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node247Generator0 else (if j.val < 2 then node247Generator1 else node247Generator2))

def node248Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node248Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,9,8,2,3,13,12,14,15,0,1,11,10,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,4,5,15,14,0,1,3,2,13,12,7,6,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node248Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,9,8,15,14,13,12,11,10,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,0,1,15,14,13,12,3,2,9,8,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node248Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node248Generator0 else (if j.val < 2 then node248Generator1 else node248Generator2))

def node249Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node249Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,3,2,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,12,13,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node249Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node249Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node249Generator0 else (if j.val < 2 then node249Generator1 else node249Generator2))

def node250Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,6,7,5,4,10,11,9,8,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,7,6,4,5,11,10,8,9,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node250Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,5,4,6,7,8,9,11,10,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node250Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,2,3,1,0,13,12,14,15,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,13,12,14,15,2,3,1,0,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node250Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node250Generator0 else (if j.val < 2 then node250Generator1 else node250Generator2))

def node251Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,4,5,6,7,8,9,10,11,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,4,5,6,7,8,9,10,11,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node251Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,9,8,10,11,5,4,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,10,11,5,4,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node251Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node251Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node251Generator0 else (if j.val < 2 then node251Generator1 else node251Generator2))

def node252Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,4,5,3,2,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,4,5,3,2,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node252Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,14,15,13,12,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node252Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,5,4,2,3,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,5,4,2,3,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node252Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node252Generator0 else (if j.val < 2 then node252Generator1 else node252Generator2))

def node253Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node253Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,5,4,3,2,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,7,6,5,4,3,2,12,13,11,10,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node253Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,7,6,1,0,14,15,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,1,0,3,2,5,4,10,11,13,12,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node253Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node253Generator0 else (if j.val < 2 then node253Generator1 else node253Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
