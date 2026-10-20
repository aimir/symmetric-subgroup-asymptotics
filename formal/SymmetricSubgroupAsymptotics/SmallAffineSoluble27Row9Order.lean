import SymmetricSubgroupAsymptotics.MetacyclicSolvabilityFactories
import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble27Row9Order

def g0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 17, 22, 1, 15, 23, 2, 16, 21, 3, 11, 25, 4, 9, 26, 5, 10, 24, 6, 14, 19, 7, 12, 20, 8, 13, 18]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 13, 16, 10, 22, 25, 19, 4, 7, 1, 26, 20, 23, 8, 2, 5, 17, 11, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 15, 21, 22, 1, 16, 17, 23, 2, 18, 6, 12, 13, 19, 7, 8, 14, 20, 9, 24, 3, 4, 10, 25, 26, 5, 11]
  invFun := ![0, 4, 8, 20, 21, 25, 10, 14, 15, 18, 22, 26, 11, 12, 16, 1, 5, 6, 9, 13, 17, 2, 3, 7, 19, 23, 24]
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
  toFun := ![0, 15, 21, 22, 1, 16, 17, 23, 2, 18, 6, 12, 13, 19, 7, 8, 14, 20, 9, 24, 3, 4, 10, 25, 26, 5, 11]
  invFun := ![0, 4, 8, 20, 21, 25, 10, 14, 15, 18, 22, 26, 11, 12, 16, 1, 5, 6, 9, 13, 17, 2, 3, 7, 19, 23, 24]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 27) where
  toFun := ![0, 24, 12, 17, 5, 20, 22, 10, 7, 1, 25, 13, 15, 3, 18, 23, 11, 8, 2, 26, 14, 16, 4, 19, 21, 9, 6]
  invFun := ![0, 9, 18, 13, 22, 4, 26, 8, 17, 25, 7, 16, 2, 11, 20, 12, 21, 3, 14, 23, 5, 24, 6, 15, 1, 10, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 27) where
  toFun := ![0, 5, 7, 12, 17, 10, 24, 20, 22, 6, 2, 4, 9, 14, 16, 21, 26, 19, 3, 8, 1, 15, 11, 13, 18, 23, 25]
  invFun := ![0, 20, 10, 18, 11, 1, 9, 2, 19, 12, 5, 22, 3, 23, 13, 21, 14, 4, 24, 17, 7, 15, 8, 25, 6, 26, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 27) where
  toFun := ![0, 20, 10, 15, 8, 25, 21, 14, 4, 22, 12, 5, 1, 18, 11, 16, 6, 26, 17, 7, 24, 23, 13, 3, 2, 19, 9]
  invFun := ![0, 12, 24, 23, 8, 11, 16, 19, 4, 26, 2, 14, 10, 22, 7, 3, 15, 18, 13, 25, 1, 6, 9, 21, 20, 5, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 27) where
  toFun := ![0, 8, 4, 10, 15, 14, 20, 25, 21, 9, 17, 13, 19, 24, 23, 2, 7, 3, 18, 26, 22, 1, 6, 5, 11, 16, 12]
  invFun := ![0, 21, 15, 17, 2, 23, 22, 16, 1, 9, 3, 24, 26, 11, 5, 4, 25, 10, 18, 12, 6, 8, 20, 14, 13, 7, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 27) where
  toFun := ![0, 8, 4, 24, 23, 19, 12, 11, 16, 17, 13, 9, 5, 1, 6, 20, 25, 21, 22, 18, 26, 10, 15, 14, 7, 3, 2]
  invFun := ![0, 13, 26, 25, 2, 12, 14, 24, 1, 11, 21, 7, 6, 10, 23, 22, 8, 9, 19, 5, 15, 17, 18, 4, 3, 16, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 27) where
  toFun := ![0, 23, 16, 4, 24, 11, 8, 19, 12, 2, 22, 15, 3, 26, 10, 7, 18, 14, 1, 21, 17, 5, 25, 9, 6, 20, 13]
  invFun := ![0, 18, 9, 12, 3, 21, 24, 15, 6, 23, 14, 5, 8, 26, 17, 11, 2, 20, 16, 7, 25, 19, 10, 1, 4, 22, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 27) where
  toFun := ![0, 19, 11, 5, 21, 13, 7, 26, 15, 12, 4, 23, 17, 6, 25, 10, 2, 18, 24, 16, 8, 20, 9, 1, 22, 14, 3]
  invFun := ![0, 23, 16, 26, 10, 3, 13, 6, 20, 22, 15, 2, 9, 5, 25, 8, 19, 12, 17, 1, 21, 4, 24, 11, 18, 14, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 27) where
  toFun := ![0, 21, 15, 11, 5, 26, 19, 13, 7, 3, 24, 9, 14, 8, 20, 22, 16, 1, 6, 18, 12, 17, 2, 23, 25, 10, 4]
  invFun := ![0, 17, 22, 9, 26, 4, 18, 8, 13, 11, 25, 3, 20, 7, 12, 2, 16, 21, 19, 6, 14, 1, 15, 23, 10, 24, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 20, 16, 3, 10, 6, 23, 15, 5, 19, 8, 22, 9, 25, 12, 2, 21, 11, 7, 14, 1, 24, 4, 18, 17]
  invFun := ![0, 22, 17, 5, 24, 10, 7, 20, 12, 14, 6, 19, 16, 2, 21, 9, 4, 26, 25, 11, 3, 18, 13, 8, 23, 15, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 27) where
  toFun := ![0, 16, 23, 13, 20, 6, 26, 3, 10, 17, 21, 1, 18, 7, 14, 4, 11, 24, 22, 2, 15, 8, 12, 19, 9, 25, 5]
  invFun := ![0, 11, 19, 7, 15, 26, 5, 13, 21, 24, 8, 16, 22, 3, 14, 20, 1, 9, 12, 23, 4, 10, 18, 2, 17, 25, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 8, 2, 5, 4, 7, 1, 10, 13, 16, 15, 9, 12, 14, 17, 11, 20, 23, 26, 25, 19, 22, 21, 24, 18]
  invFun := ![0, 8, 4, 1, 6, 5, 2, 7, 3, 13, 9, 17, 14, 10, 15, 12, 11, 16, 26, 22, 18, 24, 23, 19, 25, 21, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  invFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 27) where
  toFun := ![0, 21, 15, 8, 20, 14, 4, 25, 10, 24, 9, 3, 23, 17, 2, 19, 13, 7, 12, 6, 18, 11, 5, 26, 16, 1, 22]
  invFun := ![0, 25, 14, 11, 6, 22, 19, 17, 3, 10, 8, 21, 18, 16, 5, 2, 24, 13, 20, 15, 4, 1, 26, 12, 9, 7, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 23, 7, 9, 16, 18, 5, 4, 15, 20, 24, 2, 13, 11, 22, 6, 8, 10, 21, 19, 3, 17, 12, 26, 1]
  invFun := ![0, 26, 13, 22, 9, 8, 17, 4, 18, 5, 19, 15, 24, 14, 1, 10, 6, 23, 7, 21, 11, 20, 16, 3, 12, 2, 25]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 27) where
  toFun := ![0, 7, 5, 25, 23, 18, 14, 9, 16, 1, 8, 3, 26, 21, 19, 12, 10, 17, 2, 6, 4, 24, 22, 20, 13, 11, 15]
  invFun := ![0, 9, 18, 11, 20, 2, 19, 1, 10, 7, 16, 25, 15, 24, 6, 26, 8, 17, 5, 14, 23, 13, 22, 4, 21, 3, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 19, 10, 1, 11, 2, 20, 5, 23, 14, 21, 12, 3, 13, 4, 22, 7, 25, 16, 26, 17, 8, 15, 6, 24]
  invFun := ![0, 5, 7, 14, 16, 9, 25, 18, 23, 2, 4, 6, 13, 15, 11, 24, 20, 22, 1, 3, 8, 12, 17, 10, 26, 19, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 27) where
  toFun := ![0, 10, 20, 9, 19, 2, 18, 1, 11, 24, 7, 17, 6, 16, 26, 15, 25, 8, 12, 22, 5, 21, 4, 14, 3, 13, 23]
  invFun := ![0, 7, 5, 24, 22, 20, 12, 10, 17, 3, 1, 8, 18, 25, 23, 15, 13, 11, 6, 4, 2, 21, 19, 26, 9, 16, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 21, 22, 23, 15, 16, 17, 11, 9, 10, 5, 3, 4, 26, 24, 25, 19, 20, 18, 13, 14, 12, 7, 8, 6]
  invFun := ![0, 1, 2, 13, 14, 12, 26, 24, 25, 10, 11, 9, 23, 21, 22, 6, 7, 8, 20, 18, 19, 3, 4, 5, 16, 17, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 27) where
  toFun := ![0, 22, 17, 2, 21, 16, 1, 23, 15, 6, 19, 14, 8, 18, 13, 7, 20, 12, 3, 25, 11, 5, 24, 10, 4, 26, 9]
  invFun := ![0, 6, 3, 18, 24, 21, 9, 15, 12, 26, 23, 20, 17, 14, 11, 8, 5, 2, 13, 10, 16, 4, 1, 7, 22, 19, 25]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 26, 25, 24, 13, 12, 14, 20, 19, 18, 16, 15, 17, 3, 5, 4, 10, 9, 11, 6, 8, 7, 23, 22, 21]
  invFun := ![0, 2, 1, 15, 17, 16, 21, 23, 22, 19, 18, 20, 7, 6, 8, 13, 12, 14, 11, 10, 9, 26, 25, 24, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 1, 26, 12, 2, 24, 13, 21, 10, 8, 22, 11, 6, 23, 9, 7, 15, 4, 20, 16, 5, 18, 17, 3, 19]
  invFun := ![0, 3, 6, 25, 19, 22, 14, 17, 11, 16, 10, 13, 5, 8, 2, 18, 21, 24, 23, 26, 20, 9, 12, 15, 7, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 27) where
  toFun := ![0, 24, 12, 16, 4, 19, 23, 11, 8, 13, 1, 25, 20, 17, 5, 6, 21, 9, 26, 14, 2, 3, 18, 15, 10, 7, 22]
  invFun := ![0, 10, 20, 21, 4, 14, 15, 25, 8, 17, 24, 7, 2, 9, 19, 23, 3, 13, 22, 5, 12, 16, 26, 6, 1, 11, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 27) where
  toFun := ![0, 4, 8, 12, 16, 11, 24, 19, 23, 22, 26, 18, 7, 2, 3, 10, 14, 15, 17, 9, 13, 20, 21, 25, 5, 6, 1]
  invFun := ![0, 26, 13, 14, 1, 24, 25, 12, 2, 19, 15, 5, 3, 20, 16, 17, 4, 18, 11, 7, 21, 22, 9, 8, 6, 23, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : Equiv.Perm (Fin 27) where
  toFun := ![0, 11, 19, 3, 14, 22, 6, 17, 25, 8, 16, 24, 2, 10, 18, 5, 13, 21, 4, 12, 23, 7, 15, 26, 1, 9, 20]
  invFun := ![0, 24, 12, 3, 18, 15, 6, 21, 9, 25, 13, 1, 19, 16, 4, 22, 10, 7, 14, 2, 26, 17, 5, 20, 11, 8, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 19, 3, 17, 11, 22, 6, 20, 4, 15, 9, 23, 7, 1, 12, 26, 10, 21, 8, 2, 13, 24, 18, 5, 16]
  invFun := ![0, 15, 21, 4, 10, 25, 8, 14, 20, 12, 18, 6, 16, 22, 1, 11, 26, 5, 24, 3, 9, 19, 7, 13, 23, 2, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : Equiv.Perm (Fin 27) where
  toFun := ![0, 21, 15, 17, 2, 23, 22, 16, 1, 9, 3, 24, 26, 11, 5, 4, 25, 10, 18, 12, 6, 8, 20, 14, 13, 7, 19]
  invFun := ![0, 8, 4, 10, 15, 14, 20, 25, 21, 9, 17, 13, 19, 24, 23, 2, 7, 3, 18, 26, 22, 1, 6, 5, 11, 16, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : Equiv.Perm (Fin 27) where
  toFun := ![0, 7, 5, 21, 19, 26, 15, 13, 11, 8, 3, 1, 20, 24, 22, 14, 9, 16, 4, 2, 6, 25, 23, 18, 10, 17, 12]
  invFun := ![0, 11, 19, 10, 18, 2, 20, 1, 9, 16, 24, 8, 26, 7, 15, 6, 17, 25, 23, 4, 12, 3, 14, 22, 13, 21, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e30 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 14, 11, 17, 25, 22, 19, 23, 20, 26, 7, 4, 1, 9, 15, 12, 16, 13, 10, 18, 24, 21, 5, 2, 8]
  invFun := ![0, 14, 25, 2, 13, 24, 1, 12, 26, 15, 20, 4, 17, 19, 3, 16, 18, 5, 21, 8, 10, 23, 7, 9, 22, 6, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e31 : Equiv.Perm (Fin 27) where
  toFun := ![0, 17, 22, 7, 12, 20, 5, 10, 24, 25, 3, 11, 23, 1, 15, 18, 8, 13, 14, 19, 6, 9, 26, 4, 16, 21, 2]
  invFun := ![0, 13, 26, 10, 23, 6, 20, 3, 16, 21, 7, 11, 4, 17, 18, 14, 24, 1, 15, 19, 5, 25, 2, 12, 8, 9, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e32 : Equiv.Perm (Fin 27) where
  toFun := ![0, 12, 24, 22, 7, 10, 17, 20, 5, 2, 14, 26, 21, 6, 9, 16, 19, 4, 1, 13, 25, 23, 8, 11, 15, 18, 3]
  invFun := ![0, 18, 9, 26, 17, 8, 13, 4, 22, 14, 5, 23, 1, 19, 10, 24, 15, 6, 25, 16, 7, 12, 3, 21, 2, 20, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e33 : Equiv.Perm (Fin 27) where
  toFun := ![0, 22, 17, 18, 13, 8, 9, 4, 26, 19, 14, 6, 10, 5, 24, 1, 23, 15, 11, 3, 25, 2, 21, 16, 20, 12, 7]
  invFun := ![0, 15, 21, 19, 7, 13, 11, 26, 5, 6, 12, 18, 25, 4, 10, 17, 23, 2, 3, 9, 24, 22, 1, 16, 14, 20, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e34 : Equiv.Perm (Fin 27) where
  toFun := ![0, 13, 26, 17, 18, 4, 22, 8, 9, 7, 11, 21, 12, 25, 2, 20, 3, 16, 5, 15, 19, 10, 23, 6, 24, 1, 14]
  invFun := ![0, 25, 14, 16, 5, 18, 23, 9, 7, 8, 21, 10, 12, 1, 26, 19, 17, 3, 4, 20, 15, 11, 6, 22, 24, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e35 : Equiv.Perm (Fin 27) where
  toFun := ![0, 15, 21, 4, 10, 25, 8, 14, 20, 12, 18, 6, 16, 22, 1, 11, 26, 5, 24, 3, 9, 19, 7, 13, 23, 2, 17]
  invFun := ![0, 14, 25, 19, 3, 17, 11, 22, 6, 20, 4, 15, 9, 23, 7, 1, 12, 26, 10, 21, 8, 2, 13, 24, 18, 5, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e36 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 14, 1, 24, 25, 12, 2, 19, 15, 5, 3, 20, 16, 17, 4, 18, 11, 7, 21, 22, 9, 8, 6, 23, 10]
  invFun := ![0, 4, 8, 12, 16, 11, 24, 19, 23, 22, 26, 18, 7, 2, 3, 10, 14, 15, 17, 9, 13, 20, 21, 25, 5, 6, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e37 : Equiv.Perm (Fin 27) where
  toFun := ![0, 7, 5, 24, 22, 20, 12, 10, 17, 3, 1, 8, 18, 25, 23, 15, 13, 11, 6, 4, 2, 21, 19, 26, 9, 16, 14]
  invFun := ![0, 10, 20, 9, 19, 2, 18, 1, 11, 24, 7, 17, 6, 16, 26, 15, 25, 8, 12, 22, 5, 21, 4, 14, 3, 13, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e38 : Equiv.Perm (Fin 27) where
  toFun := ![0, 4, 8, 2, 3, 7, 1, 5, 6, 26, 18, 22, 25, 20, 21, 24, 19, 23, 13, 17, 9, 12, 16, 11, 14, 15, 10]
  invFun := ![0, 6, 3, 4, 1, 7, 8, 5, 2, 20, 26, 23, 21, 18, 24, 25, 22, 19, 10, 16, 13, 14, 11, 17, 15, 12, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e39 : Equiv.Perm (Fin 27) where
  toFun := ![0, 23, 16, 5, 25, 9, 7, 18, 14, 15, 2, 22, 11, 4, 24, 13, 6, 20, 21, 17, 1, 26, 10, 3, 19, 12, 8]
  invFun := ![0, 20, 10, 23, 13, 3, 16, 6, 26, 5, 22, 12, 25, 15, 8, 9, 2, 19, 7, 24, 17, 18, 11, 1, 14, 4, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e40 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 24, 6, 15, 12, 21, 3, 16, 25, 7, 4, 13, 22, 19, 1, 10, 23, 5, 14, 11, 20, 2, 8, 17, 26]
  invFun := ![0, 16, 23, 8, 12, 19, 4, 11, 24, 1, 17, 21, 6, 13, 20, 5, 9, 25, 2, 15, 22, 7, 14, 18, 3, 10, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e41 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 18, 24, 21, 9, 15, 12, 26, 23, 20, 17, 14, 11, 8, 5, 2, 13, 10, 16, 4, 1, 7, 22, 19, 25]
  invFun := ![0, 22, 17, 2, 21, 16, 1, 23, 15, 6, 19, 14, 8, 18, 13, 7, 20, 12, 3, 25, 11, 5, 24, 10, 4, 26, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e42 : Equiv.Perm (Fin 27) where
  toFun := ![0, 10, 20, 21, 4, 14, 15, 25, 8, 17, 24, 7, 2, 9, 19, 23, 3, 13, 22, 5, 12, 16, 26, 6, 1, 11, 18]
  invFun := ![0, 24, 12, 16, 4, 19, 23, 11, 8, 13, 1, 25, 20, 17, 5, 6, 21, 9, 26, 14, 2, 3, 18, 15, 10, 7, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e43 : Equiv.Perm (Fin 27) where
  toFun := ![0, 5, 7, 15, 11, 13, 21, 26, 19, 4, 6, 2, 10, 12, 17, 25, 18, 23, 8, 1, 3, 14, 16, 9, 20, 22, 24]
  invFun := ![0, 19, 11, 20, 9, 1, 10, 2, 18, 23, 12, 4, 13, 5, 21, 3, 22, 14, 16, 8, 24, 6, 25, 17, 26, 15, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e44 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 13, 14, 12, 26, 24, 25, 10, 11, 9, 23, 21, 22, 6, 7, 8, 20, 18, 19, 3, 4, 5, 16, 17, 15]
  invFun := ![0, 1, 2, 21, 22, 23, 15, 16, 17, 11, 9, 10, 5, 3, 4, 26, 24, 25, 19, 20, 18, 13, 14, 12, 7, 8, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e45 : Equiv.Perm (Fin 27) where
  toFun := ![0, 4, 8, 20, 21, 25, 10, 14, 15, 18, 22, 26, 11, 12, 16, 1, 5, 6, 9, 13, 17, 2, 3, 7, 19, 23, 24]
  invFun := ![0, 15, 21, 22, 1, 16, 17, 23, 2, 18, 6, 12, 13, 19, 7, 8, 14, 20, 9, 24, 3, 4, 10, 25, 26, 5, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e46 : Equiv.Perm (Fin 27) where
  toFun := ![0, 16, 23, 7, 14, 18, 5, 9, 25, 21, 1, 17, 19, 8, 12, 26, 3, 10, 15, 22, 2, 13, 20, 6, 11, 24, 4]
  invFun := ![0, 10, 20, 16, 26, 6, 23, 3, 13, 7, 17, 24, 14, 21, 4, 18, 1, 11, 5, 12, 22, 9, 19, 2, 25, 8, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e47 : Equiv.Perm (Fin 27) where
  toFun := ![0, 12, 24, 6, 9, 21, 3, 15, 18, 14, 26, 2, 11, 23, 8, 17, 20, 5, 25, 1, 13, 22, 7, 10, 19, 4, 16]
  invFun := ![0, 19, 11, 6, 25, 17, 3, 22, 14, 4, 23, 12, 1, 20, 9, 7, 26, 15, 8, 24, 16, 5, 21, 13, 2, 18, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e48 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 26, 17, 8, 13, 4, 22, 14, 5, 23, 1, 19, 10, 24, 15, 6, 25, 16, 7, 12, 3, 21, 2, 20, 11]
  invFun := ![0, 12, 24, 22, 7, 10, 17, 20, 5, 2, 14, 26, 21, 6, 9, 16, 19, 4, 1, 13, 25, 23, 8, 11, 15, 18, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e49 : Equiv.Perm (Fin 27) where
  toFun := ![0, 16, 23, 8, 12, 19, 4, 11, 24, 1, 17, 21, 6, 13, 20, 5, 9, 25, 2, 15, 22, 7, 14, 18, 3, 10, 26]
  invFun := ![0, 9, 18, 24, 6, 15, 12, 21, 3, 16, 25, 7, 4, 13, 22, 19, 1, 10, 23, 5, 14, 11, 20, 2, 8, 17, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e50 : Equiv.Perm (Fin 27) where
  toFun := ![0, 20, 10, 23, 13, 3, 16, 6, 26, 5, 22, 12, 25, 15, 8, 9, 2, 19, 7, 24, 17, 18, 11, 1, 14, 4, 21]
  invFun := ![0, 23, 16, 5, 25, 9, 7, 18, 14, 15, 2, 22, 11, 4, 24, 13, 6, 20, 21, 17, 1, 26, 10, 3, 19, 12, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e51 : Equiv.Perm (Fin 27) where
  toFun := ![0, 11, 19, 7, 15, 26, 5, 13, 21, 24, 8, 16, 22, 3, 14, 20, 1, 9, 12, 23, 4, 10, 18, 2, 17, 25, 6]
  invFun := ![0, 16, 23, 13, 20, 6, 26, 3, 10, 17, 21, 1, 18, 7, 14, 4, 11, 24, 22, 2, 15, 8, 12, 19, 9, 25, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e52 : Equiv.Perm (Fin 27) where
  toFun := ![0, 17, 22, 9, 26, 4, 18, 8, 13, 11, 25, 3, 20, 7, 12, 2, 16, 21, 19, 6, 14, 1, 15, 23, 10, 24, 5]
  invFun := ![0, 21, 15, 11, 5, 26, 19, 13, 7, 3, 24, 9, 14, 8, 20, 22, 16, 1, 6, 18, 12, 17, 2, 23, 25, 10, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e53 : Equiv.Perm (Fin 27) where
  toFun := ![0, 15, 21, 19, 7, 13, 11, 26, 5, 6, 12, 18, 25, 4, 10, 17, 23, 2, 3, 9, 24, 22, 1, 16, 14, 20, 8]
  invFun := ![0, 22, 17, 18, 13, 8, 9, 4, 26, 19, 14, 6, 10, 5, 24, 1, 23, 15, 11, 3, 25, 2, 21, 16, 20, 12, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e54 : Equiv.Perm (Fin 27) where
  toFun := ![0, 13, 26, 10, 23, 6, 20, 3, 16, 21, 7, 11, 4, 17, 18, 14, 24, 1, 15, 19, 5, 25, 2, 12, 8, 9, 22]
  invFun := ![0, 17, 22, 7, 12, 20, 5, 10, 24, 25, 3, 11, 23, 1, 15, 18, 8, 13, 14, 19, 6, 9, 26, 4, 16, 21, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e55 : Equiv.Perm (Fin 27) where
  toFun := ![0, 19, 11, 20, 9, 1, 10, 2, 18, 23, 12, 4, 13, 5, 21, 3, 22, 14, 16, 8, 24, 6, 25, 17, 26, 15, 7]
  invFun := ![0, 5, 7, 15, 11, 13, 21, 26, 19, 4, 6, 2, 10, 12, 17, 25, 18, 23, 8, 1, 3, 14, 16, 9, 20, 22, 24]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e56 : Equiv.Perm (Fin 27) where
  toFun := ![0, 8, 4, 1, 6, 5, 2, 7, 3, 13, 9, 17, 14, 10, 15, 12, 11, 16, 26, 22, 18, 24, 23, 19, 25, 21, 20]
  invFun := ![0, 3, 6, 8, 2, 5, 4, 7, 1, 10, 13, 16, 15, 9, 12, 14, 17, 11, 20, 23, 26, 25, 19, 22, 21, 24, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e57 : Equiv.Perm (Fin 27) where
  toFun := ![0, 23, 16, 26, 10, 3, 13, 6, 20, 22, 15, 2, 9, 5, 25, 8, 19, 12, 17, 1, 21, 4, 24, 11, 18, 14, 7]
  invFun := ![0, 19, 11, 5, 21, 13, 7, 26, 15, 12, 4, 23, 17, 6, 25, 10, 2, 18, 24, 16, 8, 20, 9, 1, 22, 14, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e58 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 16, 5, 18, 23, 9, 7, 8, 21, 10, 12, 1, 26, 19, 17, 3, 4, 20, 15, 11, 6, 22, 24, 13, 2]
  invFun := ![0, 13, 26, 17, 18, 4, 22, 8, 9, 7, 11, 21, 12, 25, 2, 20, 3, 16, 5, 15, 19, 10, 23, 6, 24, 1, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e59 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 4, 1, 7, 8, 5, 2, 20, 26, 23, 21, 18, 24, 25, 22, 19, 10, 16, 13, 14, 11, 17, 15, 12, 9]
  invFun := ![0, 4, 8, 2, 3, 7, 1, 5, 6, 26, 18, 22, 25, 20, 21, 24, 19, 23, 13, 17, 9, 12, 16, 11, 14, 15, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e60 : Equiv.Perm (Fin 27) where
  toFun := ![0, 10, 20, 16, 26, 6, 23, 3, 13, 7, 17, 24, 14, 21, 4, 18, 1, 11, 5, 12, 22, 9, 19, 2, 25, 8, 15]
  invFun := ![0, 16, 23, 7, 14, 18, 5, 9, 25, 21, 1, 17, 19, 8, 12, 26, 3, 10, 15, 22, 2, 13, 20, 6, 11, 24, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e61 : Equiv.Perm (Fin 27) where
  toFun := ![0, 24, 12, 3, 18, 15, 6, 21, 9, 25, 13, 1, 19, 16, 4, 22, 10, 7, 14, 2, 26, 17, 5, 20, 11, 8, 23]
  invFun := ![0, 11, 19, 3, 14, 22, 6, 17, 25, 8, 16, 24, 2, 10, 18, 5, 13, 21, 4, 12, 23, 7, 15, 26, 1, 9, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e62 : Equiv.Perm (Fin 27) where
  toFun := ![0, 5, 7, 14, 16, 9, 25, 18, 23, 2, 4, 6, 13, 15, 11, 24, 20, 22, 1, 3, 8, 12, 17, 10, 26, 19, 21]
  invFun := ![0, 18, 9, 19, 10, 1, 11, 2, 20, 5, 23, 14, 21, 12, 3, 13, 4, 22, 7, 25, 16, 26, 17, 8, 15, 6, 24]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e63 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 11, 20, 2, 19, 1, 10, 7, 16, 25, 15, 24, 6, 26, 8, 17, 5, 14, 23, 13, 22, 4, 21, 3, 12]
  invFun := ![0, 7, 5, 25, 23, 18, 14, 9, 16, 1, 8, 3, 26, 21, 19, 12, 10, 17, 2, 6, 4, 24, 22, 20, 13, 11, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e64 : Equiv.Perm (Fin 27) where
  toFun := ![0, 20, 10, 18, 11, 1, 9, 2, 19, 12, 5, 22, 3, 23, 13, 21, 14, 4, 24, 17, 7, 15, 8, 25, 6, 26, 16]
  invFun := ![0, 5, 7, 12, 17, 10, 24, 20, 22, 6, 2, 4, 9, 14, 16, 21, 26, 19, 3, 8, 1, 15, 11, 13, 18, 23, 25]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e65 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 15, 17, 16, 21, 23, 22, 19, 18, 20, 7, 6, 8, 13, 12, 14, 11, 10, 9, 26, 25, 24, 5, 4, 3]
  invFun := ![0, 2, 1, 26, 25, 24, 13, 12, 14, 20, 19, 18, 16, 15, 17, 3, 5, 4, 10, 9, 11, 6, 8, 7, 23, 22, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e66 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 2, 13, 24, 1, 12, 26, 15, 20, 4, 17, 19, 3, 16, 18, 5, 21, 8, 10, 23, 7, 9, 22, 6, 11]
  invFun := ![0, 6, 3, 14, 11, 17, 25, 22, 19, 23, 20, 26, 7, 4, 1, 9, 15, 12, 16, 13, 10, 18, 24, 21, 5, 2, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e67 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 25, 19, 22, 14, 17, 11, 16, 10, 13, 5, 8, 2, 18, 21, 24, 23, 26, 20, 9, 12, 15, 7, 1, 4]
  invFun := ![0, 25, 14, 1, 26, 12, 2, 24, 13, 21, 10, 8, 22, 11, 6, 23, 9, 7, 15, 4, 20, 16, 5, 18, 17, 3, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e68 : Equiv.Perm (Fin 27) where
  toFun := ![0, 12, 24, 23, 8, 11, 16, 19, 4, 26, 2, 14, 10, 22, 7, 3, 15, 18, 13, 25, 1, 6, 9, 21, 20, 5, 17]
  invFun := ![0, 20, 10, 15, 8, 25, 21, 14, 4, 22, 12, 5, 1, 18, 11, 16, 6, 26, 17, 7, 24, 23, 13, 3, 2, 19, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e69 : Equiv.Perm (Fin 27) where
  toFun := ![0, 19, 11, 6, 25, 17, 3, 22, 14, 4, 23, 12, 1, 20, 9, 7, 26, 15, 8, 24, 16, 5, 21, 13, 2, 18, 10]
  invFun := ![0, 12, 24, 6, 9, 21, 3, 15, 18, 14, 26, 2, 11, 23, 8, 17, 20, 5, 25, 1, 13, 22, 7, 10, 19, 4, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e70 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 11, 6, 22, 19, 17, 3, 10, 8, 21, 18, 16, 5, 2, 24, 13, 20, 15, 4, 1, 26, 12, 9, 7, 23]
  invFun := ![0, 21, 15, 8, 20, 14, 4, 25, 10, 24, 9, 3, 23, 17, 2, 19, 13, 7, 12, 6, 18, 11, 5, 26, 16, 1, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e71 : Equiv.Perm (Fin 27) where
  toFun := ![0, 11, 19, 10, 18, 2, 20, 1, 9, 16, 24, 8, 26, 7, 15, 6, 17, 25, 23, 4, 12, 3, 14, 22, 13, 21, 5]
  invFun := ![0, 7, 5, 21, 19, 26, 15, 13, 11, 8, 3, 1, 20, 24, 22, 14, 9, 16, 4, 2, 6, 25, 23, 18, 10, 17, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e72 : Equiv.Perm (Fin 27) where
  toFun := ![0, 22, 17, 5, 24, 10, 7, 20, 12, 14, 6, 19, 16, 2, 21, 9, 4, 26, 25, 11, 3, 18, 13, 8, 23, 15, 1]
  invFun := ![0, 26, 13, 20, 16, 3, 10, 6, 23, 15, 5, 19, 8, 22, 9, 25, 12, 2, 21, 11, 7, 14, 1, 24, 4, 18, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e73 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 22, 9, 8, 17, 4, 18, 5, 19, 15, 24, 14, 1, 10, 6, 23, 7, 21, 11, 20, 16, 3, 12, 2, 25]
  invFun := ![0, 14, 25, 23, 7, 9, 16, 18, 5, 4, 15, 20, 24, 2, 13, 11, 22, 6, 8, 10, 21, 19, 3, 17, 12, 26, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e74 : Equiv.Perm (Fin 27) where
  toFun := ![0, 13, 26, 25, 2, 12, 14, 24, 1, 11, 21, 7, 6, 10, 23, 22, 8, 9, 19, 5, 15, 17, 18, 4, 3, 16, 20]
  invFun := ![0, 8, 4, 24, 23, 19, 12, 11, 16, 17, 13, 9, 5, 1, 6, 20, 25, 21, 22, 18, 26, 10, 15, 14, 7, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e75 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 12, 3, 21, 24, 15, 6, 23, 14, 5, 8, 26, 17, 11, 2, 20, 16, 7, 25, 19, 10, 1, 4, 22, 13]
  invFun := ![0, 23, 16, 4, 24, 11, 8, 19, 12, 2, 22, 15, 3, 26, 10, 7, 18, 14, 1, 21, 17, 5, 25, 9, 6, 20, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e76 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 13, 16, 10, 22, 25, 19, 4, 7, 1, 26, 20, 23, 8, 2, 5, 17, 11, 14]
  invFun := ![0, 17, 22, 1, 15, 23, 2, 16, 21, 3, 11, 25, 4, 9, 26, 5, 10, 24, 6, 14, 19, 7, 12, 20, 8, 13, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e77 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 13, 22, 4, 26, 8, 17, 25, 7, 16, 2, 11, 20, 12, 21, 3, 14, 23, 5, 24, 6, 15, 1, 10, 19]
  invFun := ![0, 24, 12, 17, 5, 20, 22, 10, 7, 1, 25, 13, 15, 3, 18, 23, 11, 8, 2, 26, 14, 16, 4, 19, 21, 9, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 27) :=
  ![g0, g1]
def elements : Fin 78 → Equiv.Perm (Fin 27) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48, e49, e50, e51, e52, e53, e54, e55, e56, e57, e58, e59, e60, e61, e62, e63, e64, e65, e66, e67, e68, e69, e70, e71, e72, e73, e74, e75, e76, e77]
def next : Fin 78 → Fin 2 → Fin 78 :=
  ![![1, 2], ![3, 4], ![5, 6], ![7, 8], ![9, 10], ![11, 12], ![13, 14], ![15, 5], ![16, 17], ![18, 19], ![20, 21], ![22, 23], ![24, 25], ![26, 27], ![21, 28], ![29, 9], ![30, 26], ![31, 32], ![33, 34], ![6, 35], ![23, 36], ![32, 37], ![38, 13], ![17, 39], ![40, 41], ![35, 42], ![10, 43], ![36, 44], ![42, 45], ![46, 16], ![47, 40], ![34, 48], ![25, 49], ![2, 20], ![12, 50], ![43, 51], ![48, 52], ![51, 53], ![8, 24], ![50, 54], ![19, 55], ![14, 56], ![54, 57], ![39, 58], ![56, 59], ![59, 0], ![60, 11], ![4, 31], ![41, 61], ![58, 62], ![55, 63], ![63, 64], ![28, 65], ![65, 1], ![44, 66], ![27, 67], ![49, 68], ![68, 7], ![67, 69], ![69, 70], ![71, 18], ![37, 72], ![72, 3], ![52, 73], ![45, 15], ![66, 74], ![62, 46], ![61, 75], ![75, 76], ![53, 29], ![74, 22], ![70, 30], ![73, 77], ![57, 60], ![77, 33], ![64, 71], ![0, 38], ![76, 47]]
def words : Fin 78 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 1, 0], [0, 1, 1, 1], [1, 0, 0, 0], [1, 0, 0, 1], [1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0], [1, 1, 0, 1], [1, 1, 1, 1], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 1, 1], [1, 0, 0, 0, 0], [1, 0, 0, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 1, 1], [0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1], [0, 0, 1, 1, 1, 1], [0, 1, 0, 0, 1, 1], [0, 1, 0, 1, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 1, 1, 1], [1, 0, 0, 1, 1, 1], [1, 0, 1, 0, 0, 1], [1, 0, 1, 0, 1, 1], [1, 0, 1, 1, 1, 1], [1, 1, 0, 0, 1, 1], [1, 1, 0, 1, 1, 1], [0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 1, 1], [0, 0, 1, 1, 1, 1, 1], [0, 1, 0, 0, 1, 1, 1], [0, 1, 0, 1, 1, 1, 1], [0, 1, 1, 0, 1, 1, 1], [1, 0, 0, 1, 1, 1, 1], [1, 0, 1, 0, 0, 1, 1], [1, 0, 1, 0, 1, 1, 1], [1, 1, 0, 0, 1, 1, 1], [1, 1, 0, 1, 1, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1, 1, 1, 1], [0, 1, 1, 0, 1, 1, 1, 1], [1, 0, 1, 0, 0, 1, 1, 1], [1, 0, 1, 0, 1, 1, 1, 1], [0, 0, 1, 1, 0, 1, 1, 1, 1]]

def certificate : FiniteCayleyCertificate generators 78 where
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

theorem card : Nat.card R = 78 := certificate.card_closure elements_injective

theorem conjugates : g1*g0*g1⁻¹=g0^3 ∧ g1⁻¹*g0*g1=g0^9 := by
  constructor <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem soluble : IsSolvable R := by
  have hrange : Set.range generators = ({g0,g1} : Set (Equiv.Perm (Fin 27))) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [generators]
    · rintro (h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
  change IsSolvable (Subgroup.closure (Set.range generators))
  rw [hrange]
  exact isSolvable_closure_of_conjugate_powers g0 g1 3 9 conjugates.1 conjugates.2

end SmallAffineSoluble27Row9Order
end SymmetricSubgroupAsymptotics
