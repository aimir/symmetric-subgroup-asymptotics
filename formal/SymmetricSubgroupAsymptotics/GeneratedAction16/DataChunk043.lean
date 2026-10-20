import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
1376 through 1407. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionData16

def node1711Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1711Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,0,1,6,7,5,4,11,10,9,8,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,0,1,7,6,4,5,11,10,9,8,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1711Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1711Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,8,9,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1711Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1711Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1711Generator0 else node1711Generator1) else (if j.val < 3 then node1711Generator2 else (if j.val < 4 then node1711Generator3 else node1711Generator4)))

def node1712Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,15,14,3,2,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,9,8,10,11,13,12,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1712Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,0,1,6,7,4,5,9,8,14,15,13,12,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,1,0,6,7,4,5,9,8,15,14,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1712Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,7,6,1,0,9,8,15,14,13,12,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,1,0,3,2,5,4,9,8,14,15,13,12,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1712Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1712Generator0 else (if j.val < 2 then node1712Generator1 else node1712Generator2))

def node1713Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,13,12,14,15,8,9,11,10,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,12,13,15,14,8,9,11,10,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1713Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,8,9,11,10,12,13,15,14,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,2,3,4,5,6,7,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1713Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,11,10,1,0,7,6,12,13,2,3,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,10,11,0,1,7,6,13,12,3,2,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1713Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,6,7,1,0,2,3,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,5,4,6,7,1,0,3,2,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1713Generators (j : Fin 4) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1713Generator0 else node1713Generator1) else (if j.val < 3 then node1713Generator2 else node1713Generator3))

def node1714Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,11,10,13,12,6,7,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,10,11,12,13,7,6,9,8,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1714Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,15,14,5,4,8,9,10,11,13,12,7,6,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,15,14,5,4,13,12,6,7,8,9,11,10,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1714Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,7,6,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1714Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,12,13,14,15,1,0,2,3,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,13,12,14,15,1,0,3,2,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1714Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,11,10,13,12,7,6,9,8,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,2,3,11,10,13,12,7,6,9,8,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1714Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1714Generator0 else node1714Generator1) else (if j.val < 3 then node1714Generator2 else (if j.val < 4 then node1714Generator3 else node1714Generator4)))

def node1715Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,1,0,3,2,5,4,14,15,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,5,4,7,6,1,0,11,10,13,12,14,15,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1715Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,0,1,15,14,13,12,3,2,8,9,6,7,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,9,8,14,15,12,13,10,11,0,1,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1715Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,9,8,6,7,4,5,2,3,0,1,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,10,11,8,9,6,7,5,4,2,3,1,0,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1715Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1715Generator0 else (if j.val < 2 then node1715Generator1 else node1715Generator2))

def node1716Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,12,13,10,11,0,1,6,7,5,4,2,3,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,12,13,11,10,8,9,15,14,4,5,2,3,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1716Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,6,7,1,0,3,2,13,12,14,15,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,7,6,0,1,2,3,12,13,15,14,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1716Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,11,10,8,9,7,6,5,4,2,3,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,12,13,11,10,9,8,6,7,5,4,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1716Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1716Generator0 else (if j.val < 2 then node1716Generator1 else node1716Generator2))

def node1717Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,1,0,2,3,7,6,12,13,11,10,9,8,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,4,5,15,14,7,6,13,12,11,10,8,9,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1717Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,5,4,2,3,13,12,10,11,8,9,6,7,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,3,2,12,13,10,11,8,9,7,6,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1717Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,6,7,12,13,1,0,2,3,5,4,14,15,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,8,9,11,10,2,3,0,1,15,14,4,5,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1717Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1717Generator0 else (if j.val < 2 then node1717Generator1 else node1717Generator2))

def node1718Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,12,13,2,3,0,1,15,14,4,5,10,11,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,4,5,10,11,0,1,14,15,12,13,2,3,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1718Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,8,9,11,10,5,4,7,6,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,11,10,4,5,7,6,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1718Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,1,0,11,10,13,12,6,7,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,0,1,2,3,12,13,15,14,9,8,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1718Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1718Generator0 else (if j.val < 2 then node1718Generator1 else node1718Generator2))

def node1719Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1719Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,8,9,6,7,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,8,9,6,7,12,13,10,11,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1719Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,10,11,12,13,6,7,8,9,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,10,11,12,13,6,7,8,9,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1719Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,0,1,2,3,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,15,14,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1719Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,4,5,3,2,8,9,6,7,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,5,4,2,3,8,9,6,7,12,13,10,11,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1719Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1719Generator0 else node1719Generator1) else (if j.val < 3 then node1719Generator2 else (if j.val < 4 then node1719Generator3 else node1719Generator4)))

def node1720Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,8,9,10,11,12,13,14,15,1,0,3,2,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,15,14,1,0,2,3,4,5,6,7,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1720Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,12,13,15,14,0,1,11,10,5,4,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,3,2,13,12,15,14,1,0,11,10,4,5,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1720Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,11,10,12,13,15,14,9,8,3,2,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,13,12,14,15,0,1,11,10,5,4,6,7,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1720Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1720Generator0 else (if j.val < 2 then node1720Generator1 else node1720Generator2))

def node1721Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,2,3,4,5,6,7,8,9,10,11,12,13,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1721Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,15,14,8,9,10,11,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,0,1,2,3,13,12,6,7,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1721Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,2,3,5,4,6,7,0,1,11,10,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1721Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1721Generator0 else (if j.val < 2 then node1721Generator1 else node1721Generator2))

def node1722Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,5,4,15,14,1,0,2,3,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,7,6,14,15,0,1,2,3,5,4,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1722Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,7,6,5,4,14,15,1,0,3,2,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,7,6,5,4,14,15,0,1,2,3,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1722Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,15,14,1,0,13,12,6,7,8,9,10,11,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,0,1,8,9,10,11,12,13,7,6,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1722Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1722Generator0 else (if j.val < 2 then node1722Generator1 else node1722Generator2))

def node1723Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,4,5,7,6,1,0,2,3,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,6,7,9,8,3,2,5,4,15,14,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1723Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,5,4,15,14,9,8,2,3,13,12,6,7,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,3,2,12,13,7,6,1,0,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1723Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,3,2,13,12,6,7,1,0,11,10,4,5,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,3,2,12,13,6,7,1,0,11,10,5,4,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1723Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1723Generator0 else (if j.val < 2 then node1723Generator1 else node1723Generator2))

def node1724Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,13,12,14,15,8,9,11,10,4,5,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,12,13,15,14,8,9,11,10,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1724Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,4,5,7,6,8,9,11,10,13,12,14,15,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,0,1,2,3,5,4,6,7,9,8,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1724Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,11,10,1,0,7,6,12,13,2,3,9,8,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,10,11,0,1,7,6,13,12,3,2,8,9,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1724Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,2,3,4,5,14,15,1,0,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,2,3,4,5,14,15,0,1,10,11,13,12,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1724Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,11,10,5,4,6,7,1,0,2,3,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,10,11,5,4,6,7,1,0,3,2,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1724Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1724Generator0 else node1724Generator1) else (if j.val < 3 then node1724Generator2 else (if j.val < 4 then node1724Generator3 else node1724Generator4)))

def node1725Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,5,4,2,3,0,1,6,7,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,8,9,7,6,12,13,3,2,1,0,15,14,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1725Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,12,13,3,2,0,1,6,7,4,5,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,7,6,12,13,10,11,1,0,14,15,4,5,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1725Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,12,13,11,10,1,0,6,7,4,5,2,3,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,12,13,10,11,8,9,14,15,5,4,2,3,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1725Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1725Generator0 else (if j.val < 2 then node1725Generator1 else node1725Generator2))

def node1726Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,15,14,0,1,3,2,4,5,6,7,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,7,6,8,9,10,11,12,13,14,15,0,1,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1726Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,5,4,15,14,9,8,10,11,13,12,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,1,0,3,2,13,12,7,6,8,9,11,10,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1726Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,0,1,2,3,4,5,15,14,8,9,10,11,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,0,1,10,11,12,13,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1726Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1726Generator0 else (if j.val < 2 then node1726Generator1 else node1726Generator2))

def node1727Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,13,12,10,11,1,0,6,7,4,5,3,2,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,13,12,10,11,8,9,14,15,4,5,3,2,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1727Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,9,8,11,10,5,4,7,6,1,0,3,2,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,13,12,7,6,9,8,3,2,5,4,14,15,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1727Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,14,15,0,1,2,3,4,5,7,6,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,6,7,8,9,11,10,12,13,14,15,1,0,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1727Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1727Generator0 else (if j.val < 2 then node1727Generator1 else node1727Generator2))

def node1728Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7,9,8,10,11,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1728Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,1,0,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,3,2,0,1,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1728Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,6,7,1,0,2,3,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1728Generator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,5,4,2,3,1,0,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,4,5,3,2,0,1,9,8,11,10,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1728Generator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,12,13,14,15,3,2,1,0,6,7,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,15,14,12,13,1,0,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1728Generators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (if j.val < 2 then (if j.val < 1 then node1728Generator0 else node1728Generator1) else (if j.val < 3 then node1728Generator2 else (if j.val < 4 then node1728Generator3 else node1728Generator4)))

def node1729Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,8,9,3,2,12,13,14,15,0,1,11,10,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,5,4,14,15,1,0,2,3,13,12,6,7,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1729Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,10,11,12,13,6,7,8,9,2,3,5,4,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,10,11,13,12,6,7,8,9,2,3,4,5,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1729Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,10,11,13,12,7,6,0,1,2,3,4,5,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,7,6,1,0,2,3,5,4,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1729Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1729Generator0 else (if j.val < 2 then node1729Generator1 else node1729Generator2))

def node1730Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,7,6,4,5,3,2,0,1,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,11,10,8,9,7,6,4,5,2,3,1,0,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1730Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,6,7,1,0,10,11,5,4,15,14,8,9,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[5,4,14,15,9,8,2,3,12,13,6,7,1,0,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1730Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,5,4,7,6,0,1,11,10,12,13,15,14,8,9] : Array (Fin 16))[x.val]!
  invFun x := (#[6,7,0,1,3,2,5,4,14,15,9,8,10,11,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1730Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1730Generator0 else (if j.val < 2 then node1730Generator1 else node1730Generator2))

def node1731Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,5,4,3,2,7,6,8,9,11,10,13,12,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,5,4,3,2,7,6,8,9,11,10,13,12,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1731Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,6,7,9,8,5,4,3,2,0,1,14,15,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,7,6,2,3,5,4,14,15,0,1,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1731Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,14,15,5,4,9,8,10,11,12,13,6,7,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,15,14,5,4,12,13,7,6,8,9,10,11,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1731Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1731Generator0 else (if j.val < 2 then node1731Generator1 else node1731Generator2))

def node1732Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,11,10,4,5,7,6,8,9,2,3,13,12,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,10,11,4,5,7,6,8,9,3,2,13,12,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1732Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,2,3,4,5,6,7,1,0,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,4,5,6,7,8,9,2,3,13,12,15,14,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1732Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,0,1,11,10,4,5,15,14,8,9,3,2,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,13,12,6,7,1,0,10,11,5,4,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1732Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1732Generator0 else (if j.val < 2 then node1732Generator1 else node1732Generator2))

def node1733Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,6,7,4,5,10,11,9,8,14,15,13,12,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,15,14,4,5,2,3,9,8,6,7,13,12,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1733Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,10,11,8,9,6,7,4,5,3,2,1,0,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,11,10,8,9,6,7,4,5,2,3,1,0,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1733Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,9,8,7,6,12,13,11,10,0,1,14,15,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,0,1,14,15,5,4,3,2,9,8,6,7,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1733Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1733Generator0 else (if j.val < 2 then node1733Generator1 else node1733Generator2))

def node1734Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[7,6,5,4,2,3,8,9,15,14,12,13,10,11,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,4,5,3,2,1,0,6,7,12,13,10,11,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1734Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,3,2,0,1,14,15,12,13,11,10,8,9,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,0,1,15,14,12,13,11,10,8,9,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1734Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,13,12,15,14,9,8,10,11,5,4,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,13,12,14,15,9,8,10,11,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1734Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1734Generator0 else (if j.val < 2 then node1734Generator1 else node1734Generator2))

def node1735Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,4,5,6,7,1,0,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  invFun x := (#[7,6,1,0,2,3,4,5,9,8,10,11,12,13,14,15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1735Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[4,5,2,3,0,1,7,6,13,12,14,15,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,2,3,0,1,7,6,12,13,14,15,9,8,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1735Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,14,15,13,12,10,11,2,3,4,5,7,6,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,8,9,10,11,13,12,1,0,6,7,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1735Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1735Generator0 else (if j.val < 2 then node1735Generator1 else node1735Generator2))

def node1736Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[14,15,8,9,10,11,5,4,7,6,1,0,2,3,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,12,13,7,6,9,8,2,3,4,5,14,15,0,1] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1736Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[9,8,7,6,13,12,11,10,0,1,14,15,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,14,15,12,13,3,2,1,0,7,6,5,4,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1736Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,0,1,2,3,4,5,6,7,9,8,10,11,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[2,3,4,5,6,7,8,9,11,10,12,13,14,15,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1736Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1736Generator0 else (if j.val < 2 then node1736Generator1 else node1736Generator2))

def node1737Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,8,9,5,4,6,7,1,0,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,15,14,9,8,10,11,6,7,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1737Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[5,4,3,2,0,1,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  invFun x := (#[4,5,3,2,1,0,6,7,10,11,8,9,14,15,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1737Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[3,2,1,0,6,7,5,4,13,12,15,14,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,1,0,7,6,4,5,12,13,14,15,9,8,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1737Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1737Generator0 else (if j.val < 2 then node1737Generator1 else node1737Generator2))

def node1738Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[12,13,14,15,8,9,10,11,6,7,4,5,3,2,0,1] : Array (Fin 16))[x.val]!
  invFun x := (#[14,15,13,12,10,11,8,9,4,5,6,7,0,1,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1738Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,13,12,14,15,9,8,7,6,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,12,13,15,14,9,8,7,6,0,1,3,2,4,5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1738Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[15,14,9,8,10,11,13,12,2,3,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,8,9,15,14,13,12,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1738Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1738Generator0 else (if j.val < 2 then node1738Generator1 else node1738Generator2))

def node1739Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[6,7,8,9,11,10,14,15,5,4,2,3,1,0,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,10,11,9,8,0,1,2,3,5,4,15,14,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1739Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,7,6,3,2,4,5,15,14,1,0,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[13,12,7,6,8,9,5,4,3,2,1,0,15,14,11,10] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1739Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,12,13,7,6,5,4,15,14,0,1,3,2,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,13,12,7,6,5,4,15,14,1,0,2,3,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1739Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1739Generator0 else (if j.val < 2 then node1739Generator1 else node1739Generator2))

def node1740Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,7,6,13,12,10,11,0,1,14,15,4,5,3,2] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,15,14,12,13,3,2,0,1,6,7,5,4,10,11] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1740Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,8,9,7,6,4,5,3,2,1,0,14,15,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[11,10,9,8,6,7,5,4,2,3,0,1,15,14,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1740Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[13,12,2,3,8,9,14,15,5,4,11,10,0,1,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[12,13,2,3,9,8,15,14,4,5,11,10,1,0,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1740Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1740Generator0 else (if j.val < 2 then node1740Generator1 else node1740Generator2))

def node1741Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[10,11,12,13,15,14,8,9,3,2,0,1,7,6,4,5] : Array (Fin 16))[x.val]!
  invFun x := (#[10,11,9,8,14,15,13,12,6,7,0,1,2,3,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1741Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[2,3,1,0,6,7,4,5,10,11,13,12,14,15,9,8] : Array (Fin 16))[x.val]!
  invFun x := (#[3,2,0,1,6,7,4,5,15,14,8,9,11,10,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1741Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,13,12,15,14,3,2,4,5,7,6,1,0] : Array (Fin 16))[x.val]!
  invFun x := (#[15,14,9,8,10,11,13,12,0,1,2,3,5,4,7,6] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1741Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1741Generator0 else (if j.val < 2 then node1741Generator1 else node1741Generator2))

def node1742Generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[11,10,9,8,15,14,13,12,1,0,6,7,4,5,2,3] : Array (Fin 16))[x.val]!
  invFun x := (#[9,8,14,15,12,13,10,11,3,2,1,0,7,6,5,4] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1742Generator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1742Generator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,6,7,11,10,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,6,7,10,11,9,8,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def node1742Generators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  (if j.val < 1 then node1742Generator0 else (if j.val < 2 then node1742Generator1 else node1742Generator2))

end SymmetricSubgroupAsymptotics.BinaryActionData16
