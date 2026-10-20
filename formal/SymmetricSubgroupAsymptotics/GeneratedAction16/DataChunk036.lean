import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1152 through 1183. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1385Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,15,14,0,1,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,12,13,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1385Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1385Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,9,8,11,10,12,13,15,14,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,1,0,2,3,5,4,7,6,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1385Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1385Generator0 else (if j.val < 2 then node1385Generator1 else node1385Generator2))

def node1386Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,11,10,13,12,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,2,3,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1386Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,14,15,12,13,7,6,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,10,11,9,8,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1386Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1386Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1386Generator0 else (if j.val < 2 then node1386Generator1 else node1386Generator2))

def node1387Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1387Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,4,5,10,11,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,5,4,11,10,8,9,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1387Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,4,5,7,6,8,9,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1387Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3,15,14,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1387Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,4,5,6,7,2,3,0,1,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,4,5,6,7,3,2,1,0,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1387Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1387Generator0 else node1387Generator1) else (if j.val < 3 then node1387Generator2 else (if j.val < 4 then node1387Generator3 else node1387Generator4)))

def node1388Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,5,4,7,6,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,5,4,7,6,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1388Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,6,7,9,8,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1388Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,0,1,3,2,5,4,6,7,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,9,8,10,11,13,12,14,15,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1388Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1388Generator0 else (if j.val < 2 then node1388Generator1 else node1388Generator2))

def node1389Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,1,0,3,2,5,4,9,8,15,14,12,13,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,7,6,0,1,9,8,15,14,12,13,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1389Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,11,10,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,15,14,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1389Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,6,7,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,8,9,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1389Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1389Generator0 else (if j.val < 2 then node1389Generator1 else node1389Generator2))

def node1390Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,4,5,3,2,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,15,14,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1390Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,1,0,14,15,12,13,10,11,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1390Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1390Generator0 else node1390Generator1)

def node1391Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,9,8,10,11,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,15,14,8,9,10,11,5,4,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1391Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,4,5,6,7,9,8,3,2,12,13,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,2,3,4,5,7,6,1,0,10,11,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1391Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,9,8,10,11,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,8,9,10,11,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1391Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1391Generator0 else (if j.val < 2 then node1391Generator1 else node1391Generator2))

def node1392Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,15,14,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,14,15,1,0,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1392Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,2,3,4,5,6,7,1,0,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,4,5,6,7,8,9,2,3,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1392Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,2,3,13,12,6,7,0,1,11,10,4,5,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,2,3,12,13,6,7,1,0,11,10,5,4,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1392Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1392Generator0 else (if j.val < 2 then node1392Generator1 else node1392Generator2))

def node1393Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,4,5,2,3,14,15,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,4,5,2,3,10,11,13,12,15,14,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1393Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,11,10,8,9,15,14,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,10,11,4,5,3,2,1,0,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1393Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,12,13,3,2,5,4,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,11,10,13,12,3,2,5,4,6,7,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1393Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1393Generator0 else (if j.val < 2 then node1393Generator1 else node1393Generator2))

def node1394Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,12,13,4,5,3,2,0,1,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1394Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,6,7,1,0,14,15,8,9,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,3,2,4,5,10,11,12,13,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1394Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1394Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1394Generator0 else (if j.val < 2 then node1394Generator1 else node1394Generator2))

def node1395Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,5,4,7,6,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1395Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,8,9,11,10,13,12,14,15,1,0,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,14,15,2,3,0,1,4,5,7,6,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1395Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1395Generator0 else node1395Generator1)

def node1396Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,7,6,5,4,11,10,8,9,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,5,4,10,11,9,8,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1396Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,10,11,9,8,14,15,13,12,0,1,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,14,15,2,3,1,0,7,6,4,5,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1396Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1396Generator0 else node1396Generator1)

def node1397Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,12,13,14,15,0,1,3,2,9,8,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,0,1,2,3,13,12,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1397Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,15,14,2,3,1,0,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,14,15,12,13,2,3,1,0,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1397Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,1,0,3,2,15,14,13,12,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1397Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1397Generator0 else (if j.val < 2 then node1397Generator1 else node1397Generator2))

def node1398Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,12,13,14,15,0,1,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,14,15,13,12,2,3,1,0,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1398Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,2,3,0,1,12,13,14,15,11,10,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,0,1,2,3,15,14,13,12,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1398Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,5,4,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,7,6,4,5,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1398Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1398Generator0 else (if j.val < 2 then node1398Generator1 else node1398Generator2))

def node1399Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,14,15,13,12,1,0,2,3,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,13,12,3,2,1,0,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1399Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,10,11,9,8,13,12,14,15,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,3,2,0,1,7,6,4,5,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1399Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1399Generator0 else node1399Generator1)

def node1400Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1400Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1400Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,4,5,3,2,1,0,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,2,3,1,0,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1400Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,13,12,11,10,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,8,9,0,1,7,6,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1400Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1400Generator0 else node1400Generator1) else (if j.val < 3 then node1400Generator2 else node1400Generator3))

def node1401Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,7,6,5,4,10,11,9,8,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,7,6,5,4,11,10,8,9,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1401Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,9,8,11,10,12,13,14,15,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,2,3,0,1,5,4,7,6,8,9,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1401Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,2,3,1,0,4,5,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,8,9,10,11,12,13,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1401Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1401Generator0 else (if j.val < 2 then node1401Generator1 else node1401Generator2))

def node1402Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,3,2,5,4,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,7,6,1,0,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1402Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,11,10,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,14,15,9,8,4,5,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1402Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,2,3,4,5,12,13,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1,12,13,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1402Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1402Generator0 else (if j.val < 2 then node1402Generator1 else node1402Generator2))

def node1403Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,13,12,14,15,9,8,6,7,1,0,2,3,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,14,15,8,9,7,6,1,0,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1403Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,1,0,7,6,14,15,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,1,0,7,6,11,10,13,12,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1403Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,4,5,2,3,0,1,14,15,13,12,10,11,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,2,3,0,1,15,14,12,13,11,10,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1403Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1403Generator0 else (if j.val < 2 then node1403Generator1 else node1403Generator2))

def node1404Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,4,5,3,2,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,4,5,2,3,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1404Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,9,8,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1404Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,1,0,15,14,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,1,0,2,3,4,5,10,11,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1404Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1404Generator0 else (if j.val < 2 then node1404Generator1 else node1404Generator2))

def node1405Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1405Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,8,9,11,10,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,5,4,6,7,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1405Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,12,13,7,6,1,0,10,11,5,4,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,3,2,13,12,7,6,1,0,10,11,4,5,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1405Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1405Generator0 else (if j.val < 2 then node1405Generator1 else node1405Generator2))

def node1406Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,12,13,10,11,0,1,15,14,4,5,3,2,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,13,12,10,11,1,0,14,15,4,5,2,3,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1406Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,15,14,10,11,12,13,6,7,8,9,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,14,15,10,11,12,13,6,7,8,9,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1406Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,5,4,2,3,7,6,9,8,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,3,2,7,6,9,8,10,11,12,13,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1406Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1406Generator0 else (if j.val < 2 then node1406Generator1 else node1406Generator2))

def node1407Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,7,6,5,4,2,3,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,6,7,5,4,3,2,12,13,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1407Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,11,10,9,8,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,7,6,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1407Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,6,7,1,0,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,4,5,11,10,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1407Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1407Generator0 else (if j.val < 2 then node1407Generator1 else node1407Generator2))

def node1408Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,1,0,3,2,13,12,15,14,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,15,14,13,12,2,3,0,1,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1408Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,15,14,6,7,4,5,9,8,10,11,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,6,7,4,5,9,8,10,11,1,0,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1408Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,11,10,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1408Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1408Generator0 else (if j.val < 2 then node1408Generator1 else node1408Generator2))

def node1409Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,5,4,7,6,11,10,8,9,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,5,4,7,6,10,11,9,8,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1409Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,7,6,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,13,12,10,11,9,8,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1409Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,12,13,1,0,2,3,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,14,15,12,13,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1409Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1409Generator0 else (if j.val < 2 then node1409Generator1 else node1409Generator2))

def node1410Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,14,15,13,12,10,11,3,2,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,12,13,0,1,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1410Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,8,9,10,11,12,13,6,7,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,8,9,2,3,4,5,6,7,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1410Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,7,6,4,5,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,6,7,5,4,8,9,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1410Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1410Generator0 else (if j.val < 2 then node1410Generator1 else node1410Generator2))

def node1411Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,9,8,15,14,12,13,3,2,1,0,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,13,12,14,15,3,2,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1411Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,2,3,1,0,7,6,5,4,9,8,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,11,10,9,8,13,12,15,14,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1411Generators (j : Fin 2) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1411Generator0 else node1411Generator1)

def node1412Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1412Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1412Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1412Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,12,13,11,10,9,8,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,13,12,11,10,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1412Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,14,15,13,12,6,7,4,5,2,3,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,12,13,10,11,8,9,2,3,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1412Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1412Generator0 else node1412Generator1) else (if j.val < 3 then node1412Generator2 else (if j.val < 4 then node1412Generator3 else node1412Generator4)))

def node1413Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,8,9,15,14,12,13,0,1,3,2,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,15,14,12,13,2,3,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1413Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,6,7,4,5,8,9,10,11,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,6,7,4,5,8,9,10,11,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1413Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,12,13,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,12,13,14,15,2,3,0,1,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1413Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1413Generator0 else (if j.val < 2 then node1413Generator1 else node1413Generator2))

def node1414Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,11,10,15,14,1,0,3,2,5,4,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,11,10,13,12,0,1,14,15,5,4,2,3,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1414Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,9,8,2,3,5,4,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,6,7,9,8,2,3,5,4,14,15,1,0,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1414Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,0,1,11,10,12,13,6,7,9,8,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,14,15,0,1,10,11,13,12,7,6,8,9,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1414Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1414Generator0 else (if j.val < 2 then node1414Generator1 else node1414Generator2))

def node1415Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,15,14,12,13,11,10,0,1,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,11,10,12,13,14,15,0,1,7,6,4,5,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1415Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,15,14,12,13,2,3,4,5,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,12,13,2,3,0,1,6,7,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1415Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,8,9,10,11,4,5,3,2,1,0,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,14,15,4,5,6,7,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1415Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1415Generator0 else (if j.val < 2 then node1415Generator1 else node1415Generator2))

def node1416Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1416Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,3,2,1,0,10,11,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,5,4,3,2,1,0,11,10,8,9,14,15,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1416Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,10,11,8,9,14,15,3,2,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,15,14,13,12,4,5,2,3,0,1,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1416Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1416Generator0 else (if j.val < 2 then node1416Generator1 else node1416Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
