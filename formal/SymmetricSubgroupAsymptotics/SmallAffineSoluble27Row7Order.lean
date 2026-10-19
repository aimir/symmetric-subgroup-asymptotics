import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble27Row7Order

def g0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 17, 22, 1, 15, 23, 2, 16, 21, 3, 11, 25, 4, 9, 26, 5, 10, 24, 6, 14, 19, 7, 12, 20, 8, 13, 18]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 13, 16, 10, 22, 25, 19, 4, 7, 1, 26, 20, 23, 8, 2, 5, 17, 11, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 8, 4, 10, 15, 14, 20, 25, 21, 9, 17, 13, 19, 24, 23, 2, 7, 3, 18, 26, 22, 1, 6, 5, 11, 16, 12]
  invFun := ![0, 21, 15, 17, 2, 23, 22, 16, 1, 9, 3, 24, 26, 11, 5, 4, 25, 10, 18, 12, 6, 8, 20, 14, 13, 7, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 17, 22, 1, 15, 23, 2, 16, 21, 3, 11, 25, 4, 9, 26, 5, 10, 24, 6, 14, 19, 7, 12, 20, 8, 13, 18]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 13, 16, 10, 22, 25, 19, 4, 7, 1, 26, 20, 23, 8, 2, 5, 17, 11, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 27) where
  toFun := ![0, 8, 4, 10, 15, 14, 20, 25, 21, 9, 17, 13, 19, 24, 23, 2, 7, 3, 18, 26, 22, 1, 6, 5, 11, 16, 12]
  invFun := ![0, 21, 15, 17, 2, 23, 22, 16, 1, 9, 3, 24, 26, 11, 5, 4, 25, 10, 18, 12, 6, 8, 20, 14, 13, 7, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 27) where
  toFun := ![0, 24, 12, 17, 5, 20, 22, 10, 7, 1, 25, 13, 15, 3, 18, 23, 11, 8, 2, 26, 14, 16, 4, 19, 21, 9, 6]
  invFun := ![0, 9, 18, 13, 22, 4, 26, 8, 17, 25, 7, 16, 2, 11, 20, 12, 21, 3, 14, 23, 5, 24, 6, 15, 1, 10, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 27) where
  toFun := ![0, 21, 15, 11, 5, 26, 19, 13, 7, 3, 24, 9, 14, 8, 20, 22, 16, 1, 6, 18, 12, 17, 2, 23, 25, 10, 4]
  invFun := ![0, 17, 22, 9, 26, 4, 18, 8, 13, 11, 25, 3, 20, 7, 12, 2, 16, 21, 19, 6, 14, 1, 15, 23, 10, 24, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 8, 2, 5, 4, 7, 1, 10, 13, 16, 15, 9, 12, 14, 17, 11, 20, 23, 26, 25, 19, 22, 21, 24, 18]
  invFun := ![0, 8, 4, 1, 6, 5, 2, 7, 3, 13, 9, 17, 14, 10, 15, 12, 11, 16, 26, 22, 18, 24, 23, 19, 25, 21, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 27) where
  toFun := ![0, 21, 15, 17, 2, 23, 22, 16, 1, 9, 3, 24, 26, 11, 5, 4, 25, 10, 18, 12, 6, 8, 20, 14, 13, 7, 19]
  invFun := ![0, 8, 4, 10, 15, 14, 20, 25, 21, 9, 17, 13, 19, 24, 23, 2, 7, 3, 18, 26, 22, 1, 6, 5, 11, 16, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 27) where
  toFun := ![0, 8, 4, 24, 23, 19, 12, 11, 16, 17, 13, 9, 5, 1, 6, 20, 25, 21, 22, 18, 26, 10, 15, 14, 7, 3, 2]
  invFun := ![0, 13, 26, 25, 2, 12, 14, 24, 1, 11, 21, 7, 6, 10, 23, 22, 8, 9, 19, 5, 15, 17, 18, 4, 3, 16, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 27) where
  toFun := ![0, 7, 5, 25, 23, 18, 14, 9, 16, 1, 8, 3, 26, 21, 19, 12, 10, 17, 2, 6, 4, 24, 22, 20, 13, 11, 15]
  invFun := ![0, 9, 18, 11, 20, 2, 19, 1, 10, 7, 16, 25, 15, 24, 6, 26, 8, 17, 5, 14, 23, 13, 22, 4, 21, 3, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 21, 22, 23, 15, 16, 17, 11, 9, 10, 5, 3, 4, 26, 24, 25, 19, 20, 18, 13, 14, 12, 7, 8, 6]
  invFun := ![0, 1, 2, 13, 14, 12, 26, 24, 25, 10, 11, 9, 23, 21, 22, 6, 7, 8, 20, 18, 19, 3, 4, 5, 16, 17, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 27) where
  toFun := ![0, 7, 5, 24, 22, 20, 12, 10, 17, 3, 1, 8, 18, 25, 23, 15, 13, 11, 6, 4, 2, 21, 19, 26, 9, 16, 14]
  invFun := ![0, 10, 20, 9, 19, 2, 18, 1, 11, 24, 7, 17, 6, 16, 26, 15, 25, 8, 12, 22, 5, 21, 4, 14, 3, 13, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 27) where
  toFun := ![0, 11, 19, 3, 14, 22, 6, 17, 25, 8, 16, 24, 2, 10, 18, 5, 13, 21, 4, 12, 23, 7, 15, 26, 1, 9, 20]
  invFun := ![0, 24, 12, 3, 18, 15, 6, 21, 9, 25, 13, 1, 19, 16, 4, 22, 10, 7, 14, 2, 26, 17, 5, 20, 11, 8, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 13, 14, 12, 26, 24, 25, 10, 11, 9, 23, 21, 22, 6, 7, 8, 20, 18, 19, 3, 4, 5, 16, 17, 15]
  invFun := ![0, 1, 2, 21, 22, 23, 15, 16, 17, 11, 9, 10, 5, 3, 4, 26, 24, 25, 19, 20, 18, 13, 14, 12, 7, 8, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 27) where
  toFun := ![0, 10, 20, 21, 4, 14, 15, 25, 8, 17, 24, 7, 2, 9, 19, 23, 3, 13, 22, 5, 12, 16, 26, 6, 1, 11, 18]
  invFun := ![0, 24, 12, 16, 4, 19, 23, 11, 8, 13, 1, 25, 20, 17, 5, 6, 21, 9, 26, 14, 2, 3, 18, 15, 10, 7, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 27) where
  toFun := ![0, 21, 15, 8, 20, 14, 4, 25, 10, 24, 9, 3, 23, 17, 2, 19, 13, 7, 12, 6, 18, 11, 5, 26, 16, 1, 22]
  invFun := ![0, 25, 14, 11, 6, 22, 19, 17, 3, 10, 8, 21, 18, 16, 5, 2, 24, 13, 20, 15, 4, 1, 26, 12, 9, 7, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 27) where
  toFun := ![0, 16, 23, 13, 20, 6, 26, 3, 10, 17, 21, 1, 18, 7, 14, 4, 11, 24, 22, 2, 15, 8, 12, 19, 9, 25, 5]
  invFun := ![0, 11, 19, 7, 15, 26, 5, 13, 21, 24, 8, 16, 22, 3, 14, 20, 1, 9, 12, 23, 4, 10, 18, 2, 17, 25, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 27) where
  toFun := ![0, 17, 22, 7, 12, 20, 5, 10, 24, 25, 3, 11, 23, 1, 15, 18, 8, 13, 14, 19, 6, 9, 26, 4, 16, 21, 2]
  invFun := ![0, 13, 26, 10, 23, 6, 20, 3, 16, 21, 7, 11, 4, 17, 18, 14, 24, 1, 15, 19, 5, 25, 2, 12, 8, 9, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 27) where
  toFun := ![0, 16, 23, 8, 12, 19, 4, 11, 24, 1, 17, 21, 6, 13, 20, 5, 9, 25, 2, 15, 22, 7, 14, 18, 3, 10, 26]
  invFun := ![0, 9, 18, 24, 6, 15, 12, 21, 3, 16, 25, 7, 4, 13, 22, 19, 1, 10, 23, 5, 14, 11, 20, 2, 8, 17, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 1, 26, 12, 2, 24, 13, 21, 10, 8, 22, 11, 6, 23, 9, 7, 15, 4, 20, 16, 5, 18, 17, 3, 19]
  invFun := ![0, 3, 6, 25, 19, 22, 14, 17, 11, 16, 10, 13, 5, 8, 2, 18, 21, 24, 23, 26, 20, 9, 12, 15, 7, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 27) where
  toFun := ![0, 17, 22, 9, 26, 4, 18, 8, 13, 11, 25, 3, 20, 7, 12, 2, 16, 21, 19, 6, 14, 1, 15, 23, 10, 24, 5]
  invFun := ![0, 21, 15, 11, 5, 26, 19, 13, 7, 3, 24, 9, 14, 8, 20, 22, 16, 1, 6, 18, 12, 17, 2, 23, 25, 10, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 27) where
  toFun := ![0, 11, 19, 7, 15, 26, 5, 13, 21, 24, 8, 16, 22, 3, 14, 20, 1, 9, 12, 23, 4, 10, 18, 2, 17, 25, 6]
  invFun := ![0, 16, 23, 13, 20, 6, 26, 3, 10, 17, 21, 1, 18, 7, 14, 4, 11, 24, 22, 2, 15, 8, 12, 19, 9, 25, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 16, 5, 18, 23, 9, 7, 8, 21, 10, 12, 1, 26, 19, 17, 3, 4, 20, 15, 11, 6, 22, 24, 13, 2]
  invFun := ![0, 13, 26, 17, 18, 4, 22, 8, 9, 7, 11, 21, 12, 25, 2, 20, 3, 16, 5, 15, 19, 10, 23, 6, 24, 1, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 27) where
  toFun := ![0, 8, 4, 1, 6, 5, 2, 7, 3, 13, 9, 17, 14, 10, 15, 12, 11, 16, 26, 22, 18, 24, 23, 19, 25, 21, 20]
  invFun := ![0, 3, 6, 8, 2, 5, 4, 7, 1, 10, 13, 16, 15, 9, 12, 14, 17, 11, 20, 23, 26, 25, 19, 22, 21, 24, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 11, 6, 22, 19, 17, 3, 10, 8, 21, 18, 16, 5, 2, 24, 13, 20, 15, 4, 1, 26, 12, 9, 7, 23]
  invFun := ![0, 21, 15, 8, 20, 14, 4, 25, 10, 24, 9, 3, 23, 17, 2, 19, 13, 7, 12, 6, 18, 11, 5, 26, 16, 1, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 27) where
  toFun := ![0, 13, 26, 10, 23, 6, 20, 3, 16, 21, 7, 11, 4, 17, 18, 14, 24, 1, 15, 19, 5, 25, 2, 12, 8, 9, 22]
  invFun := ![0, 17, 22, 7, 12, 20, 5, 10, 24, 25, 3, 11, 23, 1, 15, 18, 8, 13, 14, 19, 6, 9, 26, 4, 16, 21, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 27) where
  toFun := ![0, 7, 5, 21, 19, 26, 15, 13, 11, 8, 3, 1, 20, 24, 22, 14, 9, 16, 4, 2, 6, 25, 23, 18, 10, 17, 12]
  invFun := ![0, 11, 19, 10, 18, 2, 20, 1, 9, 16, 24, 8, 26, 7, 15, 6, 17, 25, 23, 4, 12, 3, 14, 22, 13, 21, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : Equiv.Perm (Fin 27) where
  toFun := ![0, 10, 20, 9, 19, 2, 18, 1, 11, 24, 7, 17, 6, 16, 26, 15, 25, 8, 12, 22, 5, 21, 4, 14, 3, 13, 23]
  invFun := ![0, 7, 5, 24, 22, 20, 12, 10, 17, 3, 1, 8, 18, 25, 23, 15, 13, 11, 6, 4, 2, 21, 19, 26, 9, 16, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : Equiv.Perm (Fin 27) where
  toFun := ![0, 24, 12, 16, 4, 19, 23, 11, 8, 13, 1, 25, 20, 17, 5, 6, 21, 9, 26, 14, 2, 3, 18, 15, 10, 7, 22]
  invFun := ![0, 10, 20, 21, 4, 14, 15, 25, 8, 17, 24, 7, 2, 9, 19, 23, 3, 13, 22, 5, 12, 16, 26, 6, 1, 11, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : Equiv.Perm (Fin 27) where
  toFun := ![0, 13, 26, 17, 18, 4, 22, 8, 9, 7, 11, 21, 12, 25, 2, 20, 3, 16, 5, 15, 19, 10, 23, 6, 24, 1, 14]
  invFun := ![0, 25, 14, 16, 5, 18, 23, 9, 7, 8, 21, 10, 12, 1, 26, 19, 17, 3, 4, 20, 15, 11, 6, 22, 24, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : Equiv.Perm (Fin 27) where
  toFun := ![0, 24, 12, 3, 18, 15, 6, 21, 9, 25, 13, 1, 19, 16, 4, 22, 10, 7, 14, 2, 26, 17, 5, 20, 11, 8, 23]
  invFun := ![0, 11, 19, 3, 14, 22, 6, 17, 25, 8, 16, 24, 2, 10, 18, 5, 13, 21, 4, 12, 23, 7, 15, 26, 1, 9, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e30 : Equiv.Perm (Fin 27) where
  toFun := ![0, 13, 26, 25, 2, 12, 14, 24, 1, 11, 21, 7, 6, 10, 23, 22, 8, 9, 19, 5, 15, 17, 18, 4, 3, 16, 20]
  invFun := ![0, 8, 4, 24, 23, 19, 12, 11, 16, 17, 13, 9, 5, 1, 6, 20, 25, 21, 22, 18, 26, 10, 15, 14, 7, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e31 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 11, 20, 2, 19, 1, 10, 7, 16, 25, 15, 24, 6, 26, 8, 17, 5, 14, 23, 13, 22, 4, 21, 3, 12]
  invFun := ![0, 7, 5, 25, 23, 18, 14, 9, 16, 1, 8, 3, 26, 21, 19, 12, 10, 17, 2, 6, 4, 24, 22, 20, 13, 11, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e32 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 25, 19, 22, 14, 17, 11, 16, 10, 13, 5, 8, 2, 18, 21, 24, 23, 26, 20, 9, 12, 15, 7, 1, 4]
  invFun := ![0, 25, 14, 1, 26, 12, 2, 24, 13, 21, 10, 8, 22, 11, 6, 23, 9, 7, 15, 4, 20, 16, 5, 18, 17, 3, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e33 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 13, 16, 10, 22, 25, 19, 4, 7, 1, 26, 20, 23, 8, 2, 5, 17, 11, 14]
  invFun := ![0, 17, 22, 1, 15, 23, 2, 16, 21, 3, 11, 25, 4, 9, 26, 5, 10, 24, 6, 14, 19, 7, 12, 20, 8, 13, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e34 : Equiv.Perm (Fin 27) where
  toFun := ![0, 16, 23, 7, 14, 18, 5, 9, 25, 21, 1, 17, 19, 8, 12, 26, 3, 10, 15, 22, 2, 13, 20, 6, 11, 24, 4]
  invFun := ![0, 10, 20, 16, 26, 6, 23, 3, 13, 7, 17, 24, 14, 21, 4, 18, 1, 11, 5, 12, 22, 9, 19, 2, 25, 8, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e35 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 24, 6, 15, 12, 21, 3, 16, 25, 7, 4, 13, 22, 19, 1, 10, 23, 5, 14, 11, 20, 2, 8, 17, 26]
  invFun := ![0, 16, 23, 8, 12, 19, 4, 11, 24, 1, 17, 21, 6, 13, 20, 5, 9, 25, 2, 15, 22, 7, 14, 18, 3, 10, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e36 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 13, 22, 4, 26, 8, 17, 25, 7, 16, 2, 11, 20, 12, 21, 3, 14, 23, 5, 24, 6, 15, 1, 10, 19]
  invFun := ![0, 24, 12, 17, 5, 20, 22, 10, 7, 1, 25, 13, 15, 3, 18, 23, 11, 8, 2, 26, 14, 16, 4, 19, 21, 9, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e37 : Equiv.Perm (Fin 27) where
  toFun := ![0, 10, 20, 16, 26, 6, 23, 3, 13, 7, 17, 24, 14, 21, 4, 18, 1, 11, 5, 12, 22, 9, 19, 2, 25, 8, 15]
  invFun := ![0, 16, 23, 7, 14, 18, 5, 9, 25, 21, 1, 17, 19, 8, 12, 26, 3, 10, 15, 22, 2, 13, 20, 6, 11, 24, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e38 : Equiv.Perm (Fin 27) where
  toFun := ![0, 11, 19, 10, 18, 2, 20, 1, 9, 16, 24, 8, 26, 7, 15, 6, 17, 25, 23, 4, 12, 3, 14, 22, 13, 21, 5]
  invFun := ![0, 7, 5, 21, 19, 26, 15, 13, 11, 8, 3, 1, 20, 24, 22, 14, 9, 16, 4, 2, 6, 25, 23, 18, 10, 17, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 27) :=
  ![g0, g1]
def elements : Fin 39 → Equiv.Perm (Fin 27) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38]
def next : Fin 39 → Fin 2 → Fin 39 :=
  ![![1, 2], ![3, 4], ![5, 6], ![7, 8], ![9, 10], ![11, 12], ![13, 0], ![14, 15], ![16, 17], ![18, 19], ![20, 1], ![4, 21], ![22, 23], ![24, 7], ![25, 26], ![27, 13], ![28, 29], ![21, 3], ![8, 24], ![6, 30], ![31, 14], ![32, 25], ![17, 33], ![30, 5], ![12, 34], ![34, 11], ![2, 20], ![35, 22], ![15, 31], ![10, 36], ![36, 9], ![19, 37], ![29, 38], ![0, 27], ![37, 18], ![26, 32], ![33, 16], ![38, 28], ![23, 35]]
def words : Fin 39 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 0, 1, 1], [0, 1, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 1, 0, 1], [1, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 1, 1], [0, 1, 1, 0, 0, 1], [1, 0, 0, 1, 0, 1]]

def certificate : FiniteCayleyCertificate generators 39 where
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

theorem card : Nat.card R = 39 := certificate.card_closure elements_injective

end SmallAffineSoluble27Row7Order
end SymmetricSubgroupAsymptotics
