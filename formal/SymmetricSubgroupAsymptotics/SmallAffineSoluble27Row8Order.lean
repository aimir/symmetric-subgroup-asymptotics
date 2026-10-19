import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble27Row8Order

def g0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 25, 22, 19, 14, 11, 17, 9, 15, 12, 7, 4, 1, 23, 20, 26, 18, 24, 21, 16, 13, 10, 5, 2, 8]
  invFun := ![0, 14, 25, 2, 13, 24, 1, 12, 26, 9, 23, 7, 11, 22, 6, 10, 21, 8, 18, 5, 16, 20, 4, 15, 19, 3, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 25, 16, 7, 14, 5, 23, 3, 21, 12, 19, 10, 1, 17, 8, 26, 6, 24, 15, 22, 13, 4, 11, 2, 20]
  invFun := ![0, 14, 25, 9, 23, 7, 18, 5, 16, 2, 13, 24, 11, 22, 6, 20, 4, 15, 1, 12, 26, 10, 21, 8, 19, 3, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g2 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 14, 23, 5, 25, 7, 16, 1, 10, 19, 12, 21, 3, 26, 8, 17, 2, 11, 20, 13, 22, 4, 24, 6, 15]
  invFun := ![0, 9, 18, 14, 23, 5, 25, 7, 16, 1, 10, 19, 12, 21, 3, 26, 8, 17, 2, 11, 20, 13, 22, 4, 24, 6, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 25, 22, 19, 14, 11, 17, 9, 15, 12, 7, 4, 1, 23, 20, 26, 18, 24, 21, 16, 13, 10, 5, 2, 8]
  invFun := ![0, 14, 25, 2, 13, 24, 1, 12, 26, 9, 23, 7, 11, 22, 6, 10, 21, 8, 18, 5, 16, 20, 4, 15, 19, 3, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 25, 16, 7, 14, 5, 23, 3, 21, 12, 19, 10, 1, 17, 8, 26, 6, 24, 15, 22, 13, 4, 11, 2, 20]
  invFun := ![0, 14, 25, 9, 23, 7, 18, 5, 16, 2, 13, 24, 11, 22, 6, 20, 4, 15, 1, 12, 26, 10, 21, 8, 19, 3, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 14, 23, 5, 25, 7, 16, 1, 10, 19, 12, 21, 3, 26, 8, 17, 2, 11, 20, 13, 22, 4, 24, 6, 15]
  invFun := ![0, 9, 18, 14, 23, 5, 25, 7, 16, 1, 10, 19, 12, 21, 3, 26, 8, 17, 2, 11, 20, 13, 22, 4, 24, 6, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 2, 13, 24, 1, 12, 26, 9, 23, 7, 11, 22, 6, 10, 21, 8, 18, 5, 16, 20, 4, 15, 19, 3, 17]
  invFun := ![0, 6, 3, 25, 22, 19, 14, 11, 17, 9, 15, 12, 7, 4, 1, 23, 20, 26, 18, 24, 21, 16, 13, 10, 5, 2, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 2, 20, 11, 1, 19, 10, 25, 16, 7, 24, 15, 6, 26, 17, 8, 14, 5, 23, 13, 4, 22, 12, 3, 21]
  invFun := ![0, 6, 3, 25, 22, 19, 14, 11, 17, 2, 8, 5, 24, 21, 18, 13, 10, 16, 1, 7, 4, 26, 23, 20, 12, 9, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 6, 15, 24, 7, 16, 25, 8, 17, 26, 3, 12, 21, 4, 13, 22, 5, 14, 23]
  invFun := ![0, 3, 6, 18, 21, 24, 9, 12, 15, 1, 4, 7, 19, 22, 25, 10, 13, 16, 2, 5, 8, 20, 23, 26, 11, 14, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 2, 13, 24, 1, 12, 26, 3, 17, 19, 5, 16, 18, 4, 15, 20, 6, 11, 22, 8, 10, 21, 7, 9, 23]
  invFun := ![0, 6, 3, 9, 15, 12, 18, 24, 21, 25, 22, 19, 7, 4, 1, 16, 13, 10, 14, 11, 17, 23, 20, 26, 5, 2, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 2, 8, 5, 1, 7, 4, 25, 22, 19, 24, 21, 18, 26, 23, 20, 14, 11, 17, 13, 10, 16, 12, 9, 15]
  invFun := ![0, 6, 3, 2, 8, 5, 1, 7, 4, 25, 22, 19, 24, 21, 18, 26, 23, 20, 14, 11, 17, 13, 10, 16, 12, 9, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 18, 21, 24, 19, 22, 25, 20, 23, 26, 9, 12, 15, 10, 13, 16, 11, 14, 17]
  invFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 18, 21, 24, 19, 22, 25, 20, 23, 26, 9, 12, 15, 10, 13, 16, 11, 14, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 6, 22, 11, 3, 19, 17, 1, 26, 12, 7, 23, 9, 4, 20, 15, 2, 24, 13, 8, 21, 10, 5, 18, 16]
  invFun := ![0, 9, 18, 6, 15, 24, 3, 12, 21, 14, 23, 5, 11, 20, 2, 17, 26, 8, 25, 7, 16, 22, 4, 13, 19, 1, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 14, 13, 12, 11, 10, 9, 17, 16, 15, 25, 24, 26, 22, 21, 23, 19, 18, 20]
  invFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 14, 13, 12, 11, 10, 9, 17, 16, 15, 25, 24, 26, 22, 21, 23, 19, 18, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 3, 21, 12, 6, 24, 15, 2, 20, 11, 5, 23, 14, 8, 26, 17, 1, 19, 10, 4, 22, 13, 7, 25, 16]
  invFun := ![0, 18, 9, 3, 21, 12, 6, 24, 15, 2, 20, 11, 5, 23, 14, 8, 26, 17, 1, 19, 10, 4, 22, 13, 7, 25, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 6, 15, 24, 3, 12, 21, 14, 23, 5, 11, 20, 2, 17, 26, 8, 25, 7, 16, 22, 4, 13, 19, 1, 10]
  invFun := ![0, 25, 14, 6, 22, 11, 3, 19, 17, 1, 26, 12, 7, 23, 9, 4, 20, 15, 2, 24, 13, 8, 21, 10, 5, 18, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 25, 26, 24, 19, 20, 18, 22, 23, 21, 14, 12, 13, 17, 15, 16, 11, 9, 10]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 25, 26, 24, 19, 20, 18, 22, 23, 21, 14, 12, 13, 17, 15, 16, 11, 9, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 3, 17, 19, 6, 11, 22, 2, 13, 24, 5, 16, 18, 8, 10, 21, 1, 12, 26, 4, 15, 20, 7, 9, 23]
  invFun := ![0, 18, 9, 3, 21, 12, 6, 24, 15, 25, 16, 7, 19, 10, 1, 22, 13, 4, 14, 5, 23, 17, 8, 26, 11, 2, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 6, 22, 11, 3, 19, 17, 18, 16, 5, 24, 13, 2, 21, 10, 8, 9, 7, 23, 15, 4, 20, 12, 1, 26]
  invFun := ![0, 25, 14, 6, 22, 11, 3, 19, 17, 18, 16, 5, 24, 13, 2, 21, 10, 8, 9, 7, 23, 15, 4, 20, 12, 1, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 14, 13, 12, 25, 24, 26, 6, 8, 7, 11, 10, 9, 22, 21, 23, 3, 5, 4, 17, 16, 15, 19, 18, 20]
  invFun := ![0, 2, 1, 18, 20, 19, 9, 11, 10, 14, 13, 12, 5, 4, 3, 23, 22, 21, 25, 24, 26, 16, 15, 17, 7, 6, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 14, 17, 11, 25, 19, 22, 1, 4, 7, 12, 15, 9, 26, 20, 23, 2, 5, 8, 13, 16, 10, 24, 18, 21]
  invFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 14, 23, 5, 12, 21, 3, 13, 22, 4, 25, 7, 16, 26, 8, 17, 24, 6, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 9, 10, 11, 18, 19, 20, 3, 4, 5, 12, 13, 14, 21, 22, 23, 6, 7, 8, 15, 16, 17, 24, 25, 26]
  invFun := ![0, 1, 2, 9, 10, 11, 18, 19, 20, 3, 4, 5, 12, 13, 14, 21, 22, 23, 6, 7, 8, 15, 16, 17, 24, 25, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 9, 15, 12, 18, 24, 21, 2, 8, 5, 11, 17, 14, 20, 26, 23, 1, 7, 4, 10, 16, 13, 19, 25, 22]
  invFun := ![0, 18, 9, 2, 20, 11, 1, 19, 10, 3, 21, 12, 5, 23, 14, 4, 22, 13, 6, 24, 15, 8, 26, 17, 7, 25, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 18, 21, 24, 9, 12, 15, 14, 17, 11, 5, 8, 2, 23, 26, 20, 25, 19, 22, 16, 10, 13, 7, 1, 4]
  invFun := ![0, 25, 14, 1, 26, 12, 2, 24, 13, 6, 22, 11, 7, 23, 9, 8, 21, 10, 3, 19, 17, 4, 20, 15, 5, 18, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 9, 10, 11, 18, 19, 20, 25, 26, 24, 7, 8, 6, 16, 17, 15, 14, 12, 13, 23, 21, 22, 5, 3, 4]
  invFun := ![0, 1, 2, 25, 26, 24, 14, 12, 13, 3, 4, 5, 19, 20, 18, 17, 15, 16, 6, 7, 8, 22, 23, 21, 11, 9, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 9, 23, 7, 18, 5, 16, 2, 13, 24, 11, 22, 6, 20, 4, 15, 1, 12, 26, 10, 21, 8, 19, 3, 17]
  invFun := ![0, 18, 9, 25, 16, 7, 14, 5, 23, 3, 21, 12, 19, 10, 1, 17, 8, 26, 6, 24, 15, 22, 13, 4, 11, 2, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 18, 16, 5, 9, 7, 23, 6, 22, 11, 24, 13, 2, 15, 4, 20, 3, 19, 17, 21, 10, 8, 12, 1, 26]
  invFun := ![0, 25, 14, 18, 16, 5, 9, 7, 23, 6, 22, 11, 24, 13, 2, 15, 4, 20, 3, 19, 17, 21, 10, 8, 12, 1, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 14, 13, 12, 25, 24, 26, 18, 20, 19, 5, 4, 3, 16, 15, 17, 9, 11, 10, 23, 22, 21, 7, 6, 8]
  invFun := ![0, 2, 1, 14, 13, 12, 25, 24, 26, 18, 20, 19, 5, 4, 3, 16, 15, 17, 9, 11, 10, 23, 22, 21, 7, 6, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 18, 21, 24, 9, 12, 15, 1, 4, 7, 19, 22, 25, 10, 13, 16, 2, 5, 8, 20, 23, 26, 11, 14, 17]
  invFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 6, 15, 24, 7, 16, 25, 8, 17, 26, 3, 12, 21, 4, 13, 22, 5, 14, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 18, 20, 19, 9, 11, 10, 6, 8, 7, 24, 26, 25, 15, 17, 16, 3, 5, 4, 21, 23, 22, 12, 14, 13]
  invFun := ![0, 2, 1, 18, 20, 19, 9, 11, 10, 6, 8, 7, 24, 26, 25, 15, 17, 16, 3, 5, 4, 21, 23, 22, 12, 14, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 25, 22, 19, 14, 11, 17, 2, 8, 5, 24, 21, 18, 13, 10, 16, 1, 7, 4, 26, 23, 20, 12, 9, 15]
  invFun := ![0, 18, 9, 2, 20, 11, 1, 19, 10, 25, 16, 7, 24, 15, 6, 26, 17, 8, 14, 5, 23, 13, 4, 22, 12, 3, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 25, 26, 24, 14, 12, 13, 3, 4, 5, 19, 20, 18, 17, 15, 16, 6, 7, 8, 22, 23, 21, 11, 9, 10]
  invFun := ![0, 1, 2, 9, 10, 11, 18, 19, 20, 25, 26, 24, 7, 8, 6, 16, 17, 15, 14, 12, 13, 23, 21, 22, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e30 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 14, 17, 11, 12, 15, 9, 13, 16, 10, 25, 19, 22, 26, 20, 23, 24, 18, 21]
  invFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 14, 17, 11, 12, 15, 9, 13, 16, 10, 25, 19, 22, 26, 20, 23, 24, 18, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e31 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 1, 26, 12, 2, 24, 13, 6, 22, 11, 7, 23, 9, 8, 21, 10, 3, 19, 17, 4, 20, 15, 5, 18, 16]
  invFun := ![0, 3, 6, 18, 21, 24, 9, 12, 15, 14, 17, 11, 5, 8, 2, 23, 26, 20, 25, 19, 22, 16, 10, 13, 7, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e32 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 9, 15, 12, 18, 24, 21, 25, 22, 19, 7, 4, 1, 16, 13, 10, 14, 11, 17, 23, 20, 26, 5, 2, 8]
  invFun := ![0, 14, 25, 2, 13, 24, 1, 12, 26, 3, 17, 19, 5, 16, 18, 4, 15, 20, 6, 11, 22, 8, 10, 21, 7, 9, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e33 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 9, 23, 7, 18, 5, 16, 3, 17, 19, 12, 26, 1, 21, 8, 10, 6, 11, 22, 15, 20, 4, 24, 2, 13]
  invFun := ![0, 14, 25, 9, 23, 7, 18, 5, 16, 3, 17, 19, 12, 26, 1, 21, 8, 10, 6, 11, 22, 15, 20, 4, 24, 2, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e34 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 18, 16, 5, 9, 7, 23, 1, 26, 12, 19, 17, 3, 10, 8, 21, 2, 24, 13, 20, 15, 4, 11, 6, 22]
  invFun := ![0, 9, 18, 14, 23, 5, 25, 7, 16, 6, 15, 24, 11, 20, 2, 22, 4, 13, 3, 12, 21, 17, 26, 8, 19, 1, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e35 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 18, 20, 19, 9, 11, 10, 14, 13, 12, 5, 4, 3, 23, 22, 21, 25, 24, 26, 16, 15, 17, 7, 6, 8]
  invFun := ![0, 2, 1, 14, 13, 12, 25, 24, 26, 6, 8, 7, 11, 10, 9, 22, 21, 23, 3, 5, 4, 17, 16, 15, 19, 18, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e36 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 25, 16, 7, 14, 5, 23, 2, 20, 11, 24, 15, 6, 13, 4, 22, 1, 19, 10, 26, 17, 8, 12, 3, 21]
  invFun := ![0, 18, 9, 25, 16, 7, 14, 5, 23, 2, 20, 11, 24, 15, 6, 13, 4, 22, 1, 19, 10, 26, 17, 8, 12, 3, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e37 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 25, 26, 24, 14, 12, 13, 9, 10, 11, 7, 8, 6, 23, 21, 22, 18, 19, 20, 16, 17, 15, 5, 3, 4]
  invFun := ![0, 1, 2, 25, 26, 24, 14, 12, 13, 9, 10, 11, 7, 8, 6, 23, 21, 22, 18, 19, 20, 16, 17, 15, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e38 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 14, 23, 5, 12, 21, 3, 13, 22, 4, 25, 7, 16, 26, 8, 17, 24, 6, 15]
  invFun := ![0, 3, 6, 14, 17, 11, 25, 19, 22, 1, 4, 7, 12, 15, 9, 26, 20, 23, 2, 5, 8, 13, 16, 10, 24, 18, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e39 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 1, 26, 12, 2, 24, 13, 18, 16, 5, 19, 17, 3, 20, 15, 4, 9, 7, 23, 10, 8, 21, 11, 6, 22]
  invFun := ![0, 3, 6, 14, 17, 11, 25, 19, 22, 18, 21, 24, 5, 8, 2, 16, 10, 13, 9, 12, 15, 23, 26, 20, 7, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e40 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 3, 21, 12, 6, 24, 15, 25, 16, 7, 19, 10, 1, 22, 13, 4, 14, 5, 23, 17, 8, 26, 11, 2, 20]
  invFun := ![0, 14, 25, 3, 17, 19, 6, 11, 22, 2, 13, 24, 5, 16, 18, 8, 10, 21, 1, 12, 26, 4, 15, 20, 7, 9, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e41 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 3, 17, 19, 6, 11, 22, 9, 23, 7, 12, 26, 1, 15, 20, 4, 18, 5, 16, 21, 8, 10, 24, 2, 13]
  invFun := ![0, 14, 25, 3, 17, 19, 6, 11, 22, 9, 23, 7, 12, 26, 1, 15, 20, 4, 18, 5, 16, 21, 8, 10, 24, 2, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e42 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 14, 23, 5, 25, 7, 16, 6, 15, 24, 11, 20, 2, 22, 4, 13, 3, 12, 21, 17, 26, 8, 19, 1, 10]
  invFun := ![0, 25, 14, 18, 16, 5, 9, 7, 23, 1, 26, 12, 19, 17, 3, 10, 8, 21, 2, 24, 13, 20, 15, 4, 11, 6, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e43 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 14, 17, 11, 25, 19, 22, 18, 21, 24, 5, 8, 2, 16, 10, 13, 9, 12, 15, 23, 26, 20, 7, 1, 4]
  invFun := ![0, 25, 14, 1, 26, 12, 2, 24, 13, 18, 16, 5, 19, 17, 3, 20, 15, 4, 9, 7, 23, 10, 8, 21, 11, 6, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e44 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 2, 20, 11, 1, 19, 10, 3, 21, 12, 5, 23, 14, 4, 22, 13, 6, 24, 15, 8, 26, 17, 7, 25, 16]
  invFun := ![0, 6, 3, 9, 15, 12, 18, 24, 21, 2, 8, 5, 11, 17, 14, 20, 26, 23, 1, 7, 4, 10, 16, 13, 19, 25, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e45 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 2, 8, 5, 1, 7, 4, 9, 15, 12, 11, 17, 14, 10, 16, 13, 18, 24, 21, 20, 26, 23, 19, 25, 22]
  invFun := ![0, 6, 3, 2, 8, 5, 1, 7, 4, 9, 15, 12, 11, 17, 14, 10, 16, 13, 18, 24, 21, 20, 26, 23, 19, 25, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e46 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 6, 15, 24, 3, 12, 21, 1, 10, 19, 7, 16, 25, 4, 13, 22, 2, 11, 20, 8, 17, 26, 5, 14, 23]
  invFun := ![0, 9, 18, 6, 15, 24, 3, 12, 21, 1, 10, 19, 7, 16, 25, 4, 13, 22, 2, 11, 20, 8, 17, 26, 5, 14, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e47 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  invFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 3 → Equiv.Perm (Fin 27) :=
  ![g0, g1, g2]
def elements : Fin 48 → Equiv.Perm (Fin 27) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47]
def next : Fin 48 → Fin 3 → Fin 48 :=
  ![![1, 2, 3], ![4, 5, 6], ![7, 8, 9], ![10, 11, 0], ![0, 12, 13], ![14, 15, 16], ![17, 18, 1], ![19, 20, 21], ![22, 23, 24], ![25, 3, 2], ![26, 27, 22], ![21, 24, 23], ![28, 29, 25], ![30, 31, 4], ![32, 33, 34], ![20, 19, 35], ![9, 6, 5], ![24, 21, 20], ![34, 35, 19], ![2, 1, 18], ![36, 37, 17], ![38, 39, 7], ![40, 41, 10], ![12, 0, 11], ![6, 9, 8], ![16, 13, 12], ![3, 25, 29], ![42, 43, 28], ![23, 22, 27], ![33, 32, 26], ![35, 34, 33], ![27, 26, 32], ![5, 4, 31], ![44, 45, 30], ![46, 47, 14], ![13, 16, 15], ![15, 14, 47], ![41, 40, 46], ![11, 10, 41], ![47, 46, 40], ![8, 7, 39], ![45, 44, 38], ![31, 30, 45], ![39, 38, 44], ![29, 28, 43], ![37, 36, 42], ![18, 17, 37], ![43, 42, 36]]
def words : Fin 48 → List (Fin 3) :=
  ![[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [0, 0, 1], [0, 0, 2], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 0], [0, 2, 1], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 1, 0], [1, 1, 1], [1, 1, 2], [1, 2, 0], [2, 0, 0], [2, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 2, 0], [0, 0, 2, 1], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2], [0, 1, 1, 2], [1, 0, 1, 0], [1, 0, 1, 1], [1, 0, 2, 0], [1, 0, 2, 1], [1, 1, 0, 0], [1, 1, 0, 1], [2, 0, 1, 0], [2, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 0, 2, 0], [0, 1, 0, 2, 1]]

def certificate : FiniteCayleyCertificate generators 48 where
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

abbrev R : Subgroup (Equiv.Perm (Fin 27)) :=
  Subgroup.closure (Set.range generators)

theorem card : Nat.card R = 48 := certificate.card_closure elements_injective

end SmallAffineSoluble27Row8Order
end SymmetricSubgroupAsymptotics
