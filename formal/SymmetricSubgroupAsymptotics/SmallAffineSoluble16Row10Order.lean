import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row10Order

def g0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10]
  invFun := ![0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12]
  invFun := ![0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g2 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3]
  invFun := ![0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g3 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15]
  invFun := ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10]
  invFun := ![0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12]
  invFun := ![0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3]
  invFun := ![0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15]
  invFun := ![0, 1, 4, 5, 2, 3, 6, 7, 8, 9, 12, 13, 10, 11, 14, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5]
  invFun := ![0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 5, 10, 3, 12, 6, 9, 1, 14, 4, 11, 2, 13, 7, 8]
  invFun := ![0, 8, 12, 4, 10, 2, 6, 14, 15, 7, 3, 11, 5, 13, 9, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 5, 10, 12, 3, 9, 6, 4, 11, 1, 14, 8, 7, 13, 2]
  invFun := ![0, 10, 15, 5, 8, 2, 7, 13, 12, 6, 3, 9, 4, 14, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 12, 15, 1, 2, 13, 14, 4, 7, 8, 11, 5, 6, 9, 10]
  invFun := ![0, 4, 5, 1, 8, 12, 13, 9, 10, 14, 15, 11, 2, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3]
  invFun := ![0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]
  invFun := ![0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 1, 4, 10, 15, 11, 14, 2, 7, 3, 6, 8, 13, 9, 12]
  invFun := ![0, 2, 8, 10, 3, 1, 11, 9, 12, 14, 4, 6, 15, 13, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12]
  invFun := ![0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 4, 1, 10, 15, 14, 11, 8, 13, 12, 9, 2, 7, 6, 3]
  invFun := ![0, 3, 12, 15, 2, 1, 14, 13, 8, 11, 4, 7, 10, 9, 6, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 12, 15, 2, 1, 14, 13, 8, 11, 4, 7, 10, 9, 6, 5]
  invFun := ![0, 5, 4, 1, 10, 15, 14, 11, 8, 13, 12, 9, 2, 7, 6, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 15, 5, 2, 8, 13, 7, 3, 9, 12, 6, 1, 11, 14, 4]
  invFun := ![0, 12, 4, 8, 15, 3, 11, 7, 5, 9, 1, 13, 10, 6, 14, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 15, 5, 8, 2, 7, 13, 12, 6, 3, 9, 4, 14, 11, 1]
  invFun := ![0, 15, 5, 10, 12, 3, 9, 6, 4, 11, 1, 14, 8, 7, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 8, 10, 3, 1, 11, 9, 12, 14, 4, 6, 15, 13, 7, 5]
  invFun := ![0, 5, 1, 4, 10, 15, 11, 14, 2, 7, 3, 6, 8, 13, 9, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 4, 8, 15, 3, 11, 7, 5, 9, 1, 13, 10, 6, 14, 2]
  invFun := ![0, 10, 15, 5, 2, 8, 13, 7, 3, 9, 12, 6, 1, 11, 14, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 4, 8, 3, 15, 7, 11, 1, 13, 5, 9, 2, 14, 6, 10]
  invFun := ![0, 8, 12, 4, 2, 10, 14, 6, 3, 11, 15, 7, 1, 9, 13, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 3, 12, 5, 10, 6, 9, 1, 14, 2, 13, 4, 11, 7, 8]
  invFun := ![0, 8, 10, 2, 12, 4, 6, 14, 15, 7, 5, 13, 3, 11, 9, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 1, 2, 15, 12, 14, 13, 5, 6, 4, 7, 10, 9, 11, 8]
  invFun := ![0, 2, 3, 1, 10, 8, 9, 11, 15, 13, 12, 14, 5, 7, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 12, 3, 5, 10, 9, 6, 4, 11, 8, 7, 1, 14, 13, 2]
  invFun := ![0, 12, 15, 3, 8, 4, 7, 11, 10, 6, 5, 9, 2, 14, 13, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 8, 10, 1, 3, 9, 11, 4, 6, 12, 14, 5, 7, 13, 15]
  invFun := ![0, 4, 1, 5, 8, 12, 9, 13, 2, 6, 3, 7, 10, 14, 11, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 5, 1, 8, 12, 13, 9, 10, 14, 15, 11, 2, 6, 7, 3]
  invFun := ![0, 3, 12, 15, 1, 2, 13, 14, 4, 7, 8, 11, 5, 6, 9, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 1, 5, 8, 12, 9, 13, 2, 6, 3, 7, 10, 14, 11, 15]
  invFun := ![0, 2, 8, 10, 1, 3, 9, 11, 4, 6, 12, 14, 5, 7, 13, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 3, 12, 10, 5, 9, 6, 2, 13, 1, 14, 8, 7, 11, 4]
  invFun := ![0, 10, 8, 2, 15, 5, 7, 13, 12, 6, 4, 14, 3, 9, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 5, 4, 2, 3, 7, 6, 10, 11, 15, 14, 8, 9, 13, 12]
  invFun := ![0, 1, 4, 5, 3, 2, 7, 6, 12, 13, 8, 9, 15, 14, 11, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 12, 3, 10, 5, 6, 9, 8, 7, 4, 11, 2, 13, 14, 1]
  invFun := ![0, 15, 12, 3, 10, 5, 6, 9, 8, 7, 4, 11, 2, 13, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 4, 5, 3, 2, 7, 6, 12, 13, 8, 9, 15, 14, 11, 10]
  invFun := ![0, 1, 5, 4, 2, 3, 7, 6, 10, 11, 15, 14, 8, 9, 13, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e30 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5]
  invFun := ![0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e31 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 12, 4, 10, 2, 6, 14, 15, 7, 3, 11, 5, 13, 9, 1]
  invFun := ![0, 15, 5, 10, 3, 12, 6, 9, 1, 14, 4, 11, 2, 13, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e32 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 12, 4, 2, 10, 14, 6, 3, 11, 15, 7, 1, 9, 13, 5]
  invFun := ![0, 12, 4, 8, 3, 15, 7, 11, 1, 13, 5, 9, 2, 14, 6, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e33 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 2, 8, 15, 5, 13, 7, 3, 9, 1, 11, 12, 6, 14, 4]
  invFun := ![0, 10, 2, 8, 15, 5, 13, 7, 3, 9, 1, 11, 12, 6, 14, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e34 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 3, 1, 10, 8, 9, 11, 15, 13, 12, 14, 5, 7, 6, 4]
  invFun := ![0, 3, 1, 2, 15, 12, 14, 13, 5, 6, 4, 7, 10, 9, 11, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e35 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 8, 2, 15, 5, 7, 13, 12, 6, 4, 14, 3, 9, 11, 1]
  invFun := ![0, 15, 3, 12, 10, 5, 9, 6, 2, 13, 1, 14, 8, 7, 11, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e36 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 15, 3, 4, 8, 11, 7, 5, 9, 10, 6, 1, 13, 14, 2]
  invFun := ![0, 12, 15, 3, 4, 8, 11, 7, 5, 9, 10, 6, 1, 13, 14, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e37 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 3, 15, 4, 8, 7, 11, 1, 13, 2, 14, 5, 9, 6, 10]
  invFun := ![0, 8, 10, 2, 4, 12, 14, 6, 5, 13, 15, 7, 1, 9, 11, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e38 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 2, 8, 5, 15, 7, 13, 1, 11, 3, 9, 4, 14, 6, 12]
  invFun := ![0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e39 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 15, 12, 1, 2, 14, 13, 5, 6, 10, 9, 4, 7, 11, 8]
  invFun := ![0, 4, 5, 1, 12, 8, 9, 13, 15, 11, 10, 14, 3, 7, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e40 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 8, 2, 5, 15, 13, 7, 4, 14, 12, 6, 1, 11, 9, 3]
  invFun := ![0, 12, 3, 15, 8, 4, 11, 7, 2, 14, 1, 13, 10, 6, 9, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e41 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]
  invFun := ![0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e42 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 15, 3, 8, 4, 7, 11, 10, 6, 5, 9, 2, 14, 13, 1]
  invFun := ![0, 15, 12, 3, 5, 10, 9, 6, 4, 11, 8, 7, 1, 14, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e43 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 3, 15, 8, 4, 11, 7, 2, 14, 1, 13, 10, 6, 9, 5]
  invFun := ![0, 10, 8, 2, 5, 15, 13, 7, 4, 14, 12, 6, 1, 11, 9, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e44 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 1, 4, 15, 10, 14, 11, 3, 6, 2, 7, 12, 9, 13, 8]
  invFun := ![0, 2, 10, 8, 3, 1, 9, 11, 15, 13, 5, 7, 12, 14, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e45 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 10, 5, 3, 12, 9, 6, 2, 13, 8, 7, 1, 14, 11, 4]
  invFun := ![0, 12, 8, 4, 15, 3, 7, 11, 10, 6, 2, 14, 5, 9, 13, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e46 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 15, 12, 2, 1, 13, 14, 10, 9, 5, 6, 8, 11, 7, 4]
  invFun := ![0, 5, 4, 1, 15, 10, 11, 14, 12, 9, 8, 13, 3, 6, 7, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e47 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 4, 1, 15, 10, 11, 14, 12, 9, 8, 13, 3, 6, 7, 2]
  invFun := ![0, 3, 15, 12, 2, 1, 13, 14, 10, 9, 5, 6, 8, 11, 7, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e48 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 10, 5, 12, 3, 6, 9, 8, 7, 2, 13, 4, 11, 14, 1]
  invFun := ![0, 15, 10, 5, 12, 3, 6, 9, 8, 7, 2, 13, 4, 11, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e49 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 3, 2, 4, 5, 7, 6, 12, 13, 15, 14, 8, 9, 11, 10]
  invFun := ![0, 1, 3, 2, 4, 5, 7, 6, 12, 13, 15, 14, 8, 9, 11, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e50 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 10, 2, 12, 4, 6, 14, 15, 7, 5, 13, 3, 11, 9, 1]
  invFun := ![0, 15, 3, 12, 5, 10, 6, 9, 1, 14, 2, 13, 4, 11, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e51 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5]
  invFun := ![0, 10, 2, 8, 5, 15, 7, 13, 1, 11, 3, 9, 4, 14, 6, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e52 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 10, 8, 3, 1, 9, 11, 15, 13, 5, 7, 12, 14, 6, 4]
  invFun := ![0, 5, 1, 4, 15, 10, 14, 11, 3, 6, 2, 7, 12, 9, 13, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e53 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 10, 2, 4, 12, 14, 6, 5, 13, 15, 7, 1, 9, 11, 3]
  invFun := ![0, 12, 3, 15, 4, 8, 7, 11, 1, 13, 2, 14, 5, 9, 6, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e54 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 2, 10, 4, 12, 6, 14, 1, 9, 3, 11, 5, 13, 7, 15]
  invFun := ![0, 8, 2, 10, 4, 12, 6, 14, 1, 9, 3, 11, 5, 13, 7, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e55 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 5, 15, 2, 8, 7, 13, 1, 11, 4, 14, 3, 9, 6, 12]
  invFun := ![0, 8, 4, 12, 10, 2, 14, 6, 5, 13, 1, 9, 15, 7, 11, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e56 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 10, 8, 1, 3, 11, 9, 5, 7, 15, 13, 4, 6, 14, 12]
  invFun := ![0, 4, 1, 5, 12, 8, 13, 9, 3, 7, 2, 6, 15, 11, 14, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e57 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 5, 15, 8, 2, 13, 7, 4, 14, 1, 11, 12, 6, 9, 3]
  invFun := ![0, 10, 5, 15, 8, 2, 13, 7, 4, 14, 1, 11, 12, 6, 9, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e58 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 5, 1, 12, 8, 9, 13, 15, 11, 10, 14, 3, 7, 6, 2]
  invFun := ![0, 3, 15, 12, 1, 2, 14, 13, 5, 6, 10, 9, 4, 7, 11, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e59 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 8, 4, 15, 3, 7, 11, 10, 6, 2, 14, 5, 9, 13, 1]
  invFun := ![0, 15, 10, 5, 3, 12, 9, 6, 2, 13, 8, 7, 1, 14, 11, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e60 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 1, 5, 12, 8, 13, 9, 3, 7, 2, 6, 15, 11, 14, 10]
  invFun := ![0, 2, 10, 8, 1, 3, 11, 9, 5, 7, 15, 13, 4, 6, 14, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e61 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5]
  invFun := ![0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e62 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 15, 10, 1, 4, 14, 11, 3, 6, 12, 9, 2, 7, 13, 8]
  invFun := ![0, 4, 12, 8, 5, 1, 9, 13, 15, 11, 3, 7, 10, 14, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e63 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 5, 4, 3, 2, 6, 7, 15, 14, 10, 11, 12, 13, 9, 8]
  invFun := ![0, 1, 5, 4, 3, 2, 6, 7, 15, 14, 10, 11, 12, 13, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e64 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 2, 1, 15, 12, 13, 14, 10, 9, 8, 11, 5, 6, 7, 4]
  invFun := ![0, 3, 2, 1, 15, 12, 13, 14, 10, 9, 8, 11, 5, 6, 7, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e65 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 15, 10, 4, 1, 11, 14, 12, 9, 3, 6, 8, 13, 7, 2]
  invFun := ![0, 5, 15, 10, 4, 1, 11, 14, 12, 9, 3, 6, 8, 13, 7, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e66 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 4, 12, 10, 2, 14, 6, 5, 13, 1, 9, 15, 7, 11, 3]
  invFun := ![0, 10, 5, 15, 2, 8, 7, 13, 1, 11, 4, 14, 3, 9, 6, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e67 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  invFun := ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e68 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 1, 3, 10, 8, 11, 9, 5, 7, 4, 6, 15, 13, 14, 12]
  invFun := ![0, 2, 1, 3, 10, 8, 11, 9, 5, 7, 4, 6, 15, 13, 14, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e69 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 12, 8, 5, 1, 9, 13, 15, 11, 3, 7, 10, 14, 6, 2]
  invFun := ![0, 5, 15, 10, 1, 4, 14, 11, 3, 6, 12, 9, 2, 7, 13, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e70 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 12, 8, 1, 5, 13, 9, 3, 7, 15, 11, 2, 6, 14, 10]
  invFun := ![0, 4, 12, 8, 1, 5, 13, 9, 3, 7, 15, 11, 2, 6, 14, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e71 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8]
  invFun := ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![g0, g1, g2, g3]
def elements : Fin 72 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48, e49, e50, e51, e52, e53, e54, e55, e56, e57, e58, e59, e60, e61, e62, e63, e64, e65, e66, e67, e68, e69, e70, e71]
def next : Fin 72 → Fin 4 → Fin 72 :=
  ![![1, 2, 3, 4], ![5, 6, 7, 8], ![6, 9, 10, 11], ![7, 12, 0, 13], ![11, 8, 14, 0], ![0, 15, 16, 17], ![15, 18, 19, 20], ![16, 21, 1, 22], ![20, 17, 23, 1], ![18, 0, 12, 24], ![19, 3, 2, 25], ![24, 20, 26, 2], ![21, 10, 9, 27], ![27, 22, 28, 3], ![26, 29, 4, 30], ![2, 31, 32, 33], ![3, 34, 5, 35], ![33, 4, 29, 5], ![31, 1, 21, 36], ![32, 7, 6, 37], ![36, 33, 38, 6], ![34, 19, 18, 39], ![39, 35, 40, 7], ![38, 14, 8, 41], ![4, 36, 42, 9], ![13, 37, 43, 10], ![42, 44, 11, 45], ![25, 39, 46, 12], ![46, 47, 13, 48], ![44, 23, 17, 49], ![49, 45, 48, 14], ![9, 5, 34, 50], ![10, 16, 15, 51], ![50, 11, 44, 15], ![12, 32, 31, 52], ![52, 13, 47, 16], ![8, 50, 53, 18], ![22, 51, 54, 19], ![53, 26, 20, 55], ![37, 52, 56, 21], ![56, 28, 22, 57], ![30, 55, 57, 23], ![14, 58, 24, 59], ![28, 60, 25, 61], ![58, 38, 33, 62], ![62, 59, 61, 26], ![43, 63, 27, 64], ![63, 40, 35, 65], ![65, 64, 30, 28], ![41, 62, 65, 29], ![17, 24, 58, 31], ![35, 25, 60, 32], ![51, 27, 63, 34], ![23, 42, 36, 66], ![40, 43, 37, 67], ![45, 66, 67, 38], ![54, 46, 39, 68], ![48, 68, 41, 40], ![29, 53, 50, 69], ![69, 30, 64, 42], ![47, 54, 51, 70], ![70, 48, 45, 43], ![55, 69, 70, 44], ![60, 56, 52, 71], ![71, 61, 59, 46], ![57, 71, 49, 47], ![59, 41, 68, 53], ![61, 57, 55, 54], ![64, 67, 66, 56], ![66, 49, 71, 58], ![67, 65, 62, 60], ![68, 70, 69, 63]]
def words : Fin 72 → List (Fin 4) :=
  ![[], [0], [1], [2], [3], [0, 0], [0, 1], [0, 2], [0, 3], [1, 1], [1, 2], [1, 3], [2, 1], [2, 3], [3, 2], [0, 0, 1], [0, 0, 2], [0, 0, 3], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 2, 1], [0, 2, 3], [0, 3, 2], [1, 1, 3], [1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 2], [3, 2, 1], [3, 2, 3], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 2, 1], [0, 0, 2, 3], [0, 1, 1, 3], [0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 2], [0, 3, 2, 3], [1, 1, 3, 2], [1, 2, 3, 2], [1, 3, 2, 1], [1, 3, 2, 3], [2, 1, 3, 2], [2, 3, 2, 1], [2, 3, 2, 3], [3, 2, 1, 3], [0, 0, 1, 1, 3], [0, 0, 1, 2, 3], [0, 0, 2, 1, 3], [0, 1, 1, 3, 2], [0, 1, 2, 3, 2], [0, 1, 3, 2, 3], [0, 2, 1, 3, 2], [0, 2, 3, 2, 3], [1, 1, 3, 2, 1], [1, 1, 3, 2, 3], [1, 2, 3, 2, 1], [1, 2, 3, 2, 3], [1, 3, 2, 1, 3], [2, 1, 3, 2, 1], [2, 1, 3, 2, 3], [2, 3, 2, 1, 3], [0, 1, 1, 3, 2, 3], [0, 1, 2, 3, 2, 3], [0, 2, 1, 3, 2, 3], [1, 1, 3, 2, 1, 3], [1, 2, 3, 2, 1, 3], [2, 1, 3, 2, 1, 3]]

def certificate : FiniteCayleyCertificate generators 72 where
  elements := elements
  identity := 0
  identity_eq := by decide +kernel
  next := next
  next_eq := by
    intro i j
    apply Equiv.ext
    intro x
    revert i j x
    decide +kernel
  words := words
  words_eq := by
    intro i
    apply Equiv.ext
    intro x
    revert i x
    decide +kernel

theorem elements_injective : Function.Injective elements := by decide +kernel

abbrev R : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range generators)

theorem card : Nat.card R = 72 := certificate.card_closure elements_injective

end SmallAffineSoluble16Row10Order
end SymmetricSubgroupAsymptotics
