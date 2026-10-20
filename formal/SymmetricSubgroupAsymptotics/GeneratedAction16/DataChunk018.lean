import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
576 through 607. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node640Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node640Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node640Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,4,5,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node640Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node640Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,10,11,6,7,4,5,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,10,11,8,9,5,4,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node640Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node640Generator0 else node640Generator1) else (if j.val < 3 then node640Generator2 else (if j.val < 4 then node640Generator3 else node640Generator4)))

def node641Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node641Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node641Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node641Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,1,0,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,0,1,3,2,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node641Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,14,15,12,13,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,13,12,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node641Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node641Generator0 else node641Generator1) else (if j.val < 3 then node641Generator2 else (if j.val < 4 then node641Generator3 else node641Generator4)))

def node642Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node642Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node642Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node642Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node642Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,13,12,10,11,14,15,0,1,4,5,3,2,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,13,12,10,11,15,14,1,0,4,5,3,2,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node642Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node642Generator0 else node642Generator1) else (if j.val < 3 then node642Generator2 else (if j.val < 4 then node642Generator3 else node642Generator4)))

def node643Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,9,8,11,10,14,15,13,12,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,1,0,2,3,5,4,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node643Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,10,11,8,9,13,12,15,14,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,3,2,1,0,6,7,4,5,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node643Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node643Generator0 else node643Generator1)

def node644Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,5,4,2,3,14,15,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,5,4,2,3,11,10,13,12,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node644Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,15,14,9,8,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node644Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node644Generator0 else node644Generator1)

def node645Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node645Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node645Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node645Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node645Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node645Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node645Generator0 else node645Generator1) else (if j.val < 3 then node645Generator2 else (if j.val < 4 then node645Generator3 else node645Generator4)))

def node646Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,12,13,11,10,15,14,7,6,3,2,4,5,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,11,10,12,13,9,8,0,1,5,4,2,3,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node646Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node646Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,15,14,9,8,12,13,7,6,3,2,5,4,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,11,10,13,12,9,8,5,4,0,1,6,7,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node646Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node646Generator0 else (if j.val < 2 then node646Generator1 else node646Generator2))

def node647Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node647Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node647Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node647Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,2,3,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,3,2,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node647Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,13,12,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node647Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node647Generator0 else node647Generator1) else (if j.val < 3 then node647Generator2 else (if j.val < 4 then node647Generator3 else node647Generator4)))

def node648Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,10,11,12,13,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,9,8,10,11,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node648Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,1,0,7,6,11,10,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,1,0,7,6,15,14,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node648Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,11,10,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,15,14,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node648Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node648Generator0 else (if j.val < 2 then node648Generator1 else node648Generator2))

def node649Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node649Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node649Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node649Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,0,1,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,0,1,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node649Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node649Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node649Generator0 else node649Generator1) else (if j.val < 3 then node649Generator2 else (if j.val < 4 then node649Generator3 else node649Generator4)))

def node650Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,15,14,9,8,13,12,6,7,3,2,5,4,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,11,10,13,12,8,9,5,4,1,0,7,6,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node650Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node650Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node650Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node650Generator0 else (if j.val < 2 then node650Generator1 else node650Generator2))

def node651Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,9,8,11,10,14,15,13,12,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,1,0,2,3,5,4,7,6,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node651Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,3,2,0,1,6,7,4,5,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,10,11,8,9,12,13,15,14,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node651Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node651Generator0 else node651Generator1)

def node652Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node652Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node652Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node652Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node652Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node652Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node652Generator0 else node652Generator1) else (if j.val < 3 then node652Generator2 else (if j.val < 4 then node652Generator3 else node652Generator4)))

def node653Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node653Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node653Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node653Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node653Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,13,12,10,11,14,15,0,1,4,5,3,2,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,13,12,10,11,15,14,1,0,4,5,3,2,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node653Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node653Generator0 else node653Generator1) else (if j.val < 3 then node653Generator2 else (if j.val < 4 then node653Generator3 else node653Generator4)))

def node654Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node654Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node654Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node654Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node654Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,13,12,10,11,14,15,0,1,4,5,3,2,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,13,12,10,11,15,14,1,0,4,5,3,2,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node654Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node654Generator0 else node654Generator1) else (if j.val < 3 then node654Generator2 else (if j.val < 4 then node654Generator3 else node654Generator4)))

def node655Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node655Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,9,8,10,11,5,4,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,9,8,10,11,5,4,6,7,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node655Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,9,8,11,10,7,6,4,5,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,10,11,9,8,5,4,7,6,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node655Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node655Generator0 else (if j.val < 2 then node655Generator1 else node655Generator2))

def node656Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node656Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node656Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,3,2,0,1,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,0,1,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node656Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,11,10,9,8,7,6,5,4,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,11,10,9,8,7,6,5,4,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node656Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,9,8,11,10,5,4,6,7,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,9,8,10,11,5,4,7,6,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node656Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node656Generator0 else node656Generator1) else (if j.val < 3 then node656Generator2 else (if j.val < 4 then node656Generator3 else node656Generator4)))

def node657Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node657Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node657Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,7,6,5,4,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,5,4,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node657Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,1,0,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,1,0,3,2,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node657Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,13,12,10,11,14,15,0,1,4,5,3,2,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,13,12,10,11,15,14,1,0,4,5,3,2,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node657Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node657Generator0 else node657Generator1) else (if j.val < 3 then node657Generator2 else (if j.val < 4 then node657Generator3 else node657Generator4)))

def node658Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,12,13,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,8,9,2,3,5,4,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node658Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node658Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node658Generator0 else node658Generator1)

def node659Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,10,11,9,8,6,7,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,11,10,8,9,7,6,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node659Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,0,1,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node659Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,5,4,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,5,4,2,3,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node659Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node659Generator0 else (if j.val < 2 then node659Generator1 else node659Generator2))

def node660Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,13,12,15,14,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,10,11,1,0,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node660Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,15,14,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,9,8,10,11,4,5,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node660Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,1,0,15,14,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,3,2,5,4,10,11,13,12,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node660Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node660Generator0 else (if j.val < 2 then node660Generator1 else node660Generator2))

def node661Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,2,3,1,0,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,2,3,1,0,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node661Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,5,4,2,3,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node661Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,14,15,8,9,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,8,9,11,10,13,12,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node661Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node661Generator0 else (if j.val < 2 then node661Generator1 else node661Generator2))

def node662Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,14,15,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,10,11,0,1,3,2,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node662Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,12,13,15,14,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node662Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,15,14,8,9,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,11,10,12,13,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node662Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node662Generator0 else (if j.val < 2 then node662Generator1 else node662Generator2))

def node663Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,3,2,4,5,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,6,7,1,0,14,15,13,12,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node663Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,10,11,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,9,8,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node663Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node663Generator0 else node663Generator1)

def node664Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,15,14,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,8,9,4,5,2,3,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node664Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,0,1,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,0,1,2,3,5,4,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node664Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node664Generator0 else node664Generator1)

def node665Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,11,10,12,13,6,7,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,14,15,8,9,2,3,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node665Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node665Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,15,14,9,8,2,3,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,15,14,13,12,7,6,1,0,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node665Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node665Generator0 else (if j.val < 2 then node665Generator1 else node665Generator2))

def node666Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,9,8,4,5,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,11,10,7,6,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node666Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,12,13,15,14,8,9,11,10,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,13,12,14,15,8,9,11,10,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node666Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node666Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node666Generator0 else (if j.val < 2 then node666Generator1 else node666Generator2))

def node667Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,10,11,9,8,12,13,14,15,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,3,2,0,1,7,6,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node667Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,6,7,4,5,1,0,2,3,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,6,7,4,5,1,0,2,3,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node667Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,8,9,11,10,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,8,9,11,10,4,5,7,6,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node667Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node667Generator0 else (if j.val < 2 then node667Generator1 else node667Generator2))

def node668Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,1,0,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,3,2,5,4,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node668Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,15,14,12,13,11,10,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,8,9,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node668Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node668Generator0 else node668Generator1)

def node669Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,11,10,4,5,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,8,9,11,10,4,5,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node669Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,2,3,4,5,10,11,13,12,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,6,7,0,1,15,14,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node669Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node669Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node669Generator0 else (if j.val < 2 then node669Generator1 else node669Generator2))

def node670Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,12,13,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node670Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,10,11,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,4,5,6,7,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node670Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,11,10,9,8,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,14,15,13,12,7,6,5,4,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node670Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node670Generator0 else (if j.val < 2 then node670Generator1 else node670Generator2))

def node671Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,1,0,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,15,14,12,13,11,10,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node671Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,0,1,15,14,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,2,3,1,0,10,11,12,13,14,15,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node671Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node671Generator0 else node671Generator1)

end SymmetricSubgroupAsymptotics.BinaryActionData16
