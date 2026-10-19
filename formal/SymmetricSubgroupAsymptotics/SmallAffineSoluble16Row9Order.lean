import SymmetricSubgroupAsymptotics.MetacyclicSolvabilityFactories
import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row9Order

def g0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14]
  invFun := ![0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 9, 6, 2, 13, 11, 4, 8, 7, 1, 14, 10, 5, 3, 12]
  invFun := ![0, 10, 4, 14, 7, 13, 3, 9, 8, 2, 12, 6, 15, 5, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14]
  invFun := ![0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 9, 6, 2, 13, 11, 4, 8, 7, 1, 14, 10, 5, 3, 12]
  invFun := ![0, 10, 4, 14, 7, 13, 3, 9, 8, 2, 12, 6, 15, 5, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 16) where
  toFun := ![0, 13, 9, 4, 1, 12, 8, 5, 2, 15, 11, 6, 3, 14, 10, 7]
  invFun := ![0, 4, 8, 12, 3, 7, 11, 15, 6, 2, 14, 10, 5, 1, 13, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 16) where
  toFun := ![0, 14, 13, 3, 1, 15, 12, 2, 4, 10, 9, 7, 5, 11, 8, 6]
  invFun := ![0, 4, 7, 3, 8, 12, 15, 11, 14, 10, 9, 13, 6, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 16) where
  toFun := ![0, 7, 15, 8, 9, 14, 6, 1, 2, 5, 13, 10, 11, 12, 4, 3]
  invFun := ![0, 7, 8, 15, 14, 9, 6, 1, 3, 4, 11, 12, 13, 10, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 7, 11, 9, 5, 14, 2, 8, 4, 15, 3, 1, 13, 6, 10]
  invFun := ![0, 12, 7, 11, 9, 5, 14, 2, 8, 4, 15, 3, 1, 13, 6, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10]
  invFun := ![0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 14, 4, 13, 7, 3, 9, 1, 11, 15, 5, 12, 6, 2, 8]
  invFun := ![0, 8, 14, 6, 3, 11, 13, 5, 15, 7, 1, 9, 12, 4, 2, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 16) where
  toFun := ![0, 6, 10, 12, 13, 11, 7, 1, 4, 2, 14, 8, 9, 15, 3, 5]
  invFun := ![0, 7, 9, 14, 8, 15, 1, 6, 11, 12, 2, 5, 3, 4, 10, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 7, 2, 15, 10, 8, 13, 9, 12, 14, 11, 6, 3, 1, 4]
  invFun := ![0, 14, 3, 13, 15, 1, 12, 2, 6, 8, 5, 11, 9, 7, 10, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 5, 6, 15, 12, 10, 9, 2, 1, 7, 4, 13, 14, 8, 11]
  invFun := ![0, 9, 8, 1, 11, 2, 3, 10, 14, 7, 6, 15, 5, 12, 13, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 12, 8, 7, 3, 11, 15, 9, 13, 5, 1, 14, 10, 2, 6]
  invFun := ![0, 11, 14, 5, 1, 10, 15, 4, 3, 8, 13, 6, 2, 9, 12, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 4, 14, 7, 13, 3, 9, 8, 2, 12, 6, 15, 5, 11, 1]
  invFun := ![0, 15, 9, 6, 2, 13, 11, 4, 8, 7, 1, 14, 10, 5, 3, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 16) where
  toFun := ![0, 14, 15, 1, 13, 3, 2, 12, 9, 7, 6, 8, 4, 10, 11, 5]
  invFun := ![0, 3, 6, 5, 12, 15, 10, 9, 11, 8, 13, 14, 7, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 16) where
  toFun := ![0, 11, 10, 1, 14, 5, 4, 15, 13, 6, 7, 12, 3, 8, 9, 2]
  invFun := ![0, 3, 15, 12, 6, 5, 9, 10, 13, 14, 2, 1, 11, 8, 4, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 11, 3, 14, 6, 5, 13, 1, 9, 10, 2, 15, 7, 4, 12]
  invFun := ![0, 8, 11, 3, 14, 6, 5, 13, 1, 9, 10, 2, 15, 7, 4, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 6, 4, 10, 8, 12, 14, 13, 15, 11, 9, 7, 5, 1, 3]
  invFun := ![0, 14, 1, 15, 3, 13, 2, 12, 5, 11, 4, 10, 6, 8, 7, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 2, 7, 10, 15, 8, 13, 4, 1, 6, 3, 14, 11, 12, 9]
  invFun := ![0, 9, 2, 11, 8, 1, 10, 3, 6, 15, 4, 13, 14, 7, 12, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 5, 9, 7, 11, 2, 14, 15, 3, 10, 6, 8, 4, 13, 1]
  invFun := ![0, 15, 6, 9, 13, 2, 11, 4, 12, 3, 10, 5, 1, 14, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8]
  invFun := ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 16) where
  toFun := ![0, 11, 1, 10, 5, 14, 4, 15, 2, 9, 3, 8, 7, 12, 6, 13]
  invFun := ![0, 2, 8, 10, 6, 4, 14, 12, 11, 9, 3, 1, 13, 15, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 16) where
  toFun := ![0, 13, 4, 9, 12, 1, 8, 5, 7, 10, 3, 14, 11, 6, 15, 2]
  invFun := ![0, 5, 15, 10, 2, 7, 13, 8, 6, 3, 9, 12, 4, 1, 11, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 16) where
  toFun := ![0, 6, 13, 11, 12, 10, 1, 7, 9, 15, 4, 2, 5, 3, 8, 14]
  invFun := ![0, 6, 11, 13, 10, 12, 1, 7, 14, 8, 5, 3, 4, 2, 15, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 10, 8, 4, 6, 14, 12, 7, 5, 13, 15, 3, 1, 9, 11]
  invFun := ![0, 13, 1, 12, 4, 9, 5, 8, 3, 14, 2, 15, 7, 10, 6, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 16) where
  toFun := ![0, 7, 14, 9, 15, 8, 1, 6, 13, 10, 3, 4, 2, 5, 12, 11]
  invFun := ![0, 6, 12, 10, 11, 13, 7, 1, 5, 3, 9, 15, 14, 8, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : Equiv.Perm (Fin 16) where
  toFun := ![0, 6, 11, 13, 10, 12, 1, 7, 14, 8, 5, 3, 4, 2, 15, 9]
  invFun := ![0, 6, 13, 11, 12, 10, 1, 7, 9, 15, 4, 2, 5, 3, 8, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : Equiv.Perm (Fin 16) where
  toFun := ![0, 9, 8, 1, 11, 2, 3, 10, 14, 7, 6, 15, 5, 12, 13, 4]
  invFun := ![0, 3, 5, 6, 15, 12, 10, 9, 2, 1, 7, 4, 13, 14, 8, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 9, 5, 11, 7, 2, 14, 1, 13, 8, 4, 10, 6, 3, 15]
  invFun := ![0, 8, 6, 14, 11, 3, 13, 5, 10, 2, 12, 4, 1, 9, 7, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 2, 13, 6, 9, 4, 11, 10, 5, 8, 7, 12, 3, 14, 1]
  invFun := ![0, 15, 2, 13, 6, 9, 4, 11, 10, 5, 8, 7, 12, 3, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e30 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 15, 12, 6, 5, 9, 10, 13, 14, 2, 1, 11, 8, 4, 7]
  invFun := ![0, 11, 10, 1, 14, 5, 4, 15, 13, 6, 7, 12, 3, 8, 9, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e31 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 5, 4, 2, 3, 7, 6, 10, 11, 15, 14, 8, 9, 13, 12]
  invFun := ![0, 1, 4, 5, 3, 2, 7, 6, 12, 13, 8, 9, 15, 14, 11, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e32 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 12, 15, 5, 6, 9, 10, 7, 4, 11, 8, 2, 1, 14, 13]
  invFun := ![0, 13, 12, 1, 9, 4, 5, 8, 11, 6, 7, 10, 2, 15, 14, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e33 : Equiv.Perm (Fin 16) where
  toFun := ![0, 14, 1, 15, 3, 13, 2, 12, 5, 11, 4, 10, 6, 8, 7, 9]
  invFun := ![0, 2, 6, 4, 10, 8, 12, 14, 13, 15, 11, 9, 7, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e34 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 14, 6, 3, 11, 13, 5, 15, 7, 1, 9, 12, 4, 2, 10]
  invFun := ![0, 10, 14, 4, 13, 7, 3, 9, 1, 11, 15, 5, 12, 6, 2, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e35 : Equiv.Perm (Fin 16) where
  toFun := ![0, 9, 11, 2, 1, 8, 10, 3, 5, 12, 14, 7, 4, 13, 15, 6]
  invFun := ![0, 4, 3, 7, 12, 8, 15, 11, 5, 1, 6, 2, 9, 13, 10, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e36 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 13, 7, 4, 14, 9, 3, 12, 6, 1, 11, 8, 2, 5, 15]
  invFun := ![0, 10, 13, 7, 4, 14, 9, 3, 12, 6, 1, 11, 8, 2, 5, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e37 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 6, 9, 13, 2, 11, 4, 12, 3, 10, 5, 1, 14, 7, 8]
  invFun := ![0, 12, 5, 9, 7, 11, 2, 14, 15, 3, 10, 6, 8, 4, 13, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e38 : Equiv.Perm (Fin 16) where
  toFun := ![0, 11, 5, 14, 10, 1, 15, 4, 7, 12, 2, 9, 13, 6, 8, 3]
  invFun := ![0, 5, 10, 15, 7, 2, 13, 8, 14, 11, 4, 1, 9, 12, 3, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e39 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12]
  invFun := ![0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e40 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 6, 14, 11, 3, 13, 5, 10, 2, 12, 4, 1, 9, 7, 15]
  invFun := ![0, 12, 9, 5, 11, 7, 2, 14, 1, 13, 8, 4, 10, 6, 3, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e41 : Equiv.Perm (Fin 16) where
  toFun := ![0, 7, 9, 14, 8, 15, 1, 6, 11, 12, 2, 5, 3, 4, 10, 13]
  invFun := ![0, 6, 10, 12, 13, 11, 7, 1, 4, 2, 14, 8, 9, 15, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e42 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 7, 3, 8, 12, 15, 11, 14, 10, 9, 13, 6, 2, 1, 5]
  invFun := ![0, 14, 13, 3, 1, 15, 12, 2, 4, 10, 9, 7, 5, 11, 8, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e43 : Equiv.Perm (Fin 16) where
  toFun := ![0, 13, 12, 1, 9, 4, 5, 8, 11, 6, 7, 10, 2, 15, 14, 3]
  invFun := ![0, 3, 12, 15, 5, 6, 9, 10, 7, 4, 11, 8, 2, 1, 14, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e44 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 15, 10, 2, 7, 13, 8, 6, 3, 9, 12, 4, 1, 11, 14]
  invFun := ![0, 13, 4, 9, 12, 1, 8, 5, 7, 10, 3, 14, 11, 6, 15, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e45 : Equiv.Perm (Fin 16) where
  toFun := ![0, 14, 3, 13, 15, 1, 12, 2, 6, 8, 5, 11, 9, 7, 10, 4]
  invFun := ![0, 5, 7, 2, 15, 10, 8, 13, 9, 12, 14, 11, 6, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e46 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8]
  invFun := ![0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e47 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 3, 7, 12, 8, 15, 11, 5, 1, 6, 2, 9, 13, 10, 14]
  invFun := ![0, 9, 11, 2, 1, 8, 10, 3, 5, 12, 14, 7, 4, 13, 15, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e48 : Equiv.Perm (Fin 16) where
  toFun := ![0, 11, 14, 5, 1, 10, 15, 4, 3, 8, 13, 6, 2, 9, 12, 7]
  invFun := ![0, 4, 12, 8, 7, 3, 11, 15, 9, 13, 5, 1, 14, 10, 2, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e49 : Equiv.Perm (Fin 16) where
  toFun := ![0, 7, 8, 15, 14, 9, 6, 1, 3, 4, 11, 12, 13, 10, 5, 2]
  invFun := ![0, 7, 15, 8, 9, 14, 6, 1, 2, 5, 13, 10, 11, 12, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e50 : Equiv.Perm (Fin 16) where
  toFun := ![0, 6, 12, 10, 11, 13, 7, 1, 5, 3, 9, 15, 14, 8, 2, 4]
  invFun := ![0, 7, 14, 9, 15, 8, 1, 6, 13, 10, 3, 4, 2, 5, 12, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e51 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1]
  invFun := ![0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e52 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 10, 15, 7, 2, 13, 8, 14, 11, 4, 1, 9, 12, 3, 6]
  invFun := ![0, 11, 5, 14, 10, 1, 15, 4, 7, 12, 2, 9, 13, 6, 8, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e53 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 8, 10, 6, 4, 14, 12, 11, 9, 3, 1, 13, 15, 5, 7]
  invFun := ![0, 11, 1, 10, 5, 14, 4, 15, 2, 9, 3, 8, 7, 12, 6, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e54 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 6, 5, 12, 15, 10, 9, 11, 8, 13, 14, 7, 4, 1, 2]
  invFun := ![0, 14, 15, 1, 13, 3, 2, 12, 9, 7, 6, 8, 4, 10, 11, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e55 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 3, 7, 11, 15, 6, 2, 14, 10, 5, 1, 13, 9]
  invFun := ![0, 13, 9, 4, 1, 12, 8, 5, 2, 15, 11, 6, 3, 14, 10, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e56 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 4, 5, 3, 2, 7, 6, 12, 13, 8, 9, 15, 14, 11, 10]
  invFun := ![0, 1, 5, 4, 2, 3, 7, 6, 10, 11, 15, 14, 8, 9, 13, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e57 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13]
  invFun := ![0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e58 : Equiv.Perm (Fin 16) where
  toFun := ![0, 9, 2, 11, 8, 1, 10, 3, 6, 15, 4, 13, 14, 7, 12, 5]
  invFun := ![0, 5, 2, 7, 10, 15, 8, 13, 4, 1, 6, 3, 14, 11, 12, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e59 : Equiv.Perm (Fin 16) where
  toFun := ![0, 13, 1, 12, 4, 9, 5, 8, 3, 14, 2, 15, 7, 10, 6, 11]
  invFun := ![0, 2, 10, 8, 4, 6, 14, 12, 7, 5, 13, 15, 3, 1, 9, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 16) :=
  ![g0, g1]
def elements : Fin 60 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48, e49, e50, e51, e52, e53, e54, e55, e56, e57, e58, e59]
def next : Fin 60 → Fin 2 → Fin 60 :=
  ![![1, 2], ![3, 4], ![5, 6], ![7, 5], ![8, 9], ![10, 11], ![12, 13], ![14, 8], ![15, 16], ![17, 18], ![19, 12], ![20, 21], ![22, 23], ![24, 0], ![25, 10], ![26, 17], ![27, 28], ![29, 30], ![31, 1], ![32, 20], ![33, 34], ![35, 3], ![36, 24], ![37, 14], ![18, 38], ![39, 15], ![40, 27], ![41, 42], ![43, 7], ![44, 31], ![45, 25], ![21, 46], ![47, 22], ![48, 35], ![49, 39], ![28, 50], ![9, 37], ![30, 51], ![46, 32], ![52, 19], ![53, 29], ![6, 43], ![13, 52], ![23, 54], ![11, 45], ![34, 55], ![50, 40], ![56, 33], ![16, 49], ![42, 57], ![54, 47], ![55, 56], ![38, 26], ![58, 41], ![51, 53], ![57, 58], ![59, 36], ![0, 59], ![2, 44], ![4, 48]]
def words : Fin 60 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1], [0, 0, 0, 0], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 1, 0], [0, 1, 1, 1], [1, 0, 0, 0], [1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0], [1, 1, 0, 1], [1, 1, 1, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 1, 1, 0], [1, 0, 0, 0, 0], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 1, 0, 0, 0], [1, 1, 0, 1, 0], [1, 1, 1, 0, 1], [0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0], [0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0], [0, 1, 1, 0, 1, 0], [0, 1, 1, 1, 0, 1], [1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1], [1, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 1], [0, 1, 1, 0, 1, 0, 1], [1, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]

def certificate : FiniteCayleyCertificate generators 60 where
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

theorem card : Nat.card R = 60 := certificate.card_closure elements_injective

theorem conjugates : g1*g0*g1⁻¹=g0^2 ∧ g1⁻¹*g0*g1=g0^8 := by
  constructor <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem soluble : IsSolvable R := by
  have hrange : Set.range generators = ({g0,g1} : Set (Equiv.Perm (Fin 16))) := by
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
  exact isSolvable_closure_of_conjugate_powers g0 g1 2 8 conjugates.1 conjugates.2

end SmallAffineSoluble16Row9Order
end SymmetricSubgroupAsymptotics
