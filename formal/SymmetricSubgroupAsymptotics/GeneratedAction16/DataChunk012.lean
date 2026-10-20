import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
384 through 415. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node448Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node448Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node448Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,1,0,12,13,14,15,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,2,3,14,15,12,13,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node448Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,1,0,15,14,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,1,0,2,3,13,12,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node448Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,0,1,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,14,15,12,13,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node448Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node448Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node448Generator0 else (if j.val < 2 then node448Generator1 else node448Generator2)) else (if j.val < 4 then node448Generator3 else (if j.val < 5 then node448Generator4 else node448Generator5)))

def node449Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node449Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node449Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node449Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node449Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node449Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node449Generator0 else node449Generator1) else (if j.val < 3 then node449Generator2 else (if j.val < 4 then node449Generator3 else node449Generator4)))

def node450Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node450Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node450Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node450Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node450Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node450Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node450Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node450Generator0 else (if j.val < 2 then node450Generator1 else node450Generator2)) else (if j.val < 4 then node450Generator3 else (if j.val < 5 then node450Generator4 else node450Generator5)))

def node451Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node451Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node451Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node451Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node451Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node451Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node451Generator0 else node451Generator1) else (if j.val < 3 then node451Generator2 else (if j.val < 4 then node451Generator3 else node451Generator4)))

def node452Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node452Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node452Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node452Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node452Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node452Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node452Generator0 else node452Generator1) else (if j.val < 3 then node452Generator2 else (if j.val < 4 then node452Generator3 else node452Generator4)))

def node453Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node453Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node453Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node453Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,15,14,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,1,0,3,2,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node453Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,9,8,10,11,7,6,5,4,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,11,10,9,8,5,4,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node453Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node453Generator0 else node453Generator1) else (if j.val < 3 then node453Generator2 else (if j.val < 4 then node453Generator3 else node453Generator4)))

def node454Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node454Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,0,1,3,2,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,2,3,1,0,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node454Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,0,1,2,3,14,15,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,1,0,12,13,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node454Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,12,13,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node454Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,15,14,13,12,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,12,13,14,15,0,1,3,2,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node454Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node454Generator0 else node454Generator1) else (if j.val < 3 then node454Generator2 else (if j.val < 4 then node454Generator3 else node454Generator4)))

def node455Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node455Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node455Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node455Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,2,3,0,1,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node455Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node455Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node455Generator0 else node455Generator1) else (if j.val < 3 then node455Generator2 else (if j.val < 4 then node455Generator3 else node455Generator4)))

def node456Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node456Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node456Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node456Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node456Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node456Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node456Generator0 else node456Generator1) else (if j.val < 3 then node456Generator2 else (if j.val < 4 then node456Generator3 else node456Generator4)))

def node457Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node457Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,7,6,4,5,9,8,11,10,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,6,7,5,4,9,8,11,10,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node457Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,11,10,9,8,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node457Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,3,2,1,0,14,15,13,12,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,1,0,2,3,13,12,15,14,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node457Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node457Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node457Generator0 else node457Generator1) else (if j.val < 3 then node457Generator2 else (if j.val < 4 then node457Generator3 else node457Generator4)))

def node458Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node458Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node458Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node458Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node458Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,5,4,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,11,10,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node458Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node458Generator0 else node458Generator1) else (if j.val < 3 then node458Generator2 else (if j.val < 4 then node458Generator3 else node458Generator4)))

def node459Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node459Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node459Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node459Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node459Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node459Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node459Generator0 else node459Generator1) else (if j.val < 3 then node459Generator2 else (if j.val < 4 then node459Generator3 else node459Generator4)))

def node460Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node460Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node460Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node460Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,2,3,0,1,14,15,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,3,2,12,13,14,15,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node460Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node460Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node460Generator0 else node460Generator1) else (if j.val < 3 then node460Generator2 else (if j.val < 4 then node460Generator3 else node460Generator4)))

def node461Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node461Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node461Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node461Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node461Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node461Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node461Generator0 else node461Generator1) else (if j.val < 3 then node461Generator2 else (if j.val < 4 then node461Generator3 else node461Generator4)))

def node462Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node462Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node462Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node462Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node462Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node462Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,13,12,15,14,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node462Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node462Generator0 else (if j.val < 2 then node462Generator1 else node462Generator2)) else (if j.val < 4 then node462Generator3 else (if j.val < 5 then node462Generator4 else node462Generator5)))

def node463Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node463Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node463Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node463Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,2,3,0,1,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,1,0,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node463Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,0,1,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,12,13,15,14,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node463Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node463Generator0 else node463Generator1) else (if j.val < 3 then node463Generator2 else (if j.val < 4 then node463Generator3 else node463Generator4)))

def node464Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node464Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node464Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node464Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,2,3,0,1,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,1,0,3,2,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node464Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node464Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node464Generator0 else node464Generator1) else (if j.val < 3 then node464Generator2 else (if j.val < 4 then node464Generator3 else node464Generator4)))

def node465Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,5,4,7,6,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node465Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,1,0,3,2,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,2,3,0,1,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node465Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,5,4,6,7,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,9,8,10,11,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node465Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node465Generator0 else (if j.val < 2 then node465Generator1 else node465Generator2))

def node466Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node466Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node466Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node466Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node466Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node466Generator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node466Generators (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (if j.val < 3 then (if j.val < 1 then node466Generator0 else (if j.val < 2 then node466Generator1 else node466Generator2)) else (if j.val < 4 then node466Generator3 else (if j.val < 5 then node466Generator4 else node466Generator5)))

def node467Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node467Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node467Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node467Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node467Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,14,15,5,4,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,11,10,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node467Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node467Generator0 else node467Generator1) else (if j.val < 3 then node467Generator2 else (if j.val < 4 then node467Generator3 else node467Generator4)))

def node468Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node468Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,7,6,8,9,11,10,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node468Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node468Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node468Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node468Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node468Generator0 else node468Generator1) else (if j.val < 3 then node468Generator2 else (if j.val < 4 then node468Generator3 else node468Generator4)))

def node469Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node469Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node469Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,5,4,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node469Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,12,13,14,15,3,2,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node469Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,13,12,0,1,2,3,4,5,7,6,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,11,10,14,15,12,13,3,2,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node469Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node469Generator0 else node469Generator1) else (if j.val < 3 then node469Generator2 else (if j.val < 4 then node469Generator3 else node469Generator4)))

def node470Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node470Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,12,13,15,14,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node470Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,13,12,15,14,1,0,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,12,13,2,3,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node470Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,13,12,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,12,13,14,15,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node470Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node470Generator0 else node470Generator1) else (if j.val < 3 then node470Generator2 else node470Generator3))

def node471Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node471Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node471Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,5,4,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,7,6,4,5,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node471Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,0,1,3,2,13,12,15,14,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node471Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,13,12,15,14,5,4,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,9,8,11,10,0,1,3,2,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node471Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node471Generator0 else node471Generator1) else (if j.val < 3 then node471Generator2 else (if j.val < 4 then node471Generator3 else node471Generator4)))

def node472Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node472Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node472Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node472Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node472Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node472Generator0 else node472Generator1) else (if j.val < 3 then node472Generator2 else node472Generator3))

def node473Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node473Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node473Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node473Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,11,10,9,8,15,14,4,5,2,3,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,8,9,14,15,5,4,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node473Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node473Generator0 else node473Generator1) else (if j.val < 3 then node473Generator2 else node473Generator3))

def node474Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,3,2,0,1,13,12,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,0,1,2,3,15,14,13,12,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node474Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,6,7,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,6,7,9,8,10,11,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node474Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,6,7,4,5,11,10,9,8,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,6,7,4,5,11,10,9,8,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node474Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node474Generator0 else (if j.val < 2 then node474Generator1 else node474Generator2))

def node475Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node475Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node475Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,10,11,8,9,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node475Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,13,12,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node475Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,14,15,12,13,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,3,2,0,1,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node475Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node475Generator0 else node475Generator1) else (if j.val < 3 then node475Generator2 else (if j.val < 4 then node475Generator3 else node475Generator4)))

def node476Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node476Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,5,4,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node476Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node476Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,0,1,13,12,15,14,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,2,3,14,15,12,13,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node476Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,14,15,12,13,3,2,1,0,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,15,14,1,0,3,2,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node476Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node476Generator0 else node476Generator1) else (if j.val < 3 then node476Generator2 else (if j.val < 4 then node476Generator3 else node476Generator4)))

def node477Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node477Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,6,7,12,13,10,11,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node477Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,15,14,13,12,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,14,15,12,13,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node477Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,1,0,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node477Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node477Generator0 else node477Generator1) else (if j.val < 3 then node477Generator2 else node477Generator3))

def node478Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,7,6,4,5,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,4,5,3,2,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node478Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,5,4,3,2,0,1,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node478Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,9,8,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,13,12,10,11,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node478Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node478Generator0 else (if j.val < 2 then node478Generator1 else node478Generator2))

def node479Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node479Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,9,8,11,10,5,4,7,6,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node479Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,0,1,2,3,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,3,2,0,1,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node479Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,3,2,0,1,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,13,12,14,15,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node479Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node479Generator0 else node479Generator1) else (if j.val < 3 then node479Generator2 else node479Generator3))

end SymmetricSubgroupAsymptotics.BinaryActionData16
