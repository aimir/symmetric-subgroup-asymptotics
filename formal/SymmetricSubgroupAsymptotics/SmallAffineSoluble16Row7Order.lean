import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row7Order

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
  toFun := ![0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5]
  invFun := ![0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5]
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
  toFun := ![0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5]
  invFun := ![0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5]
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
  toFun := ![0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]
  invFun := ![0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]
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
  toFun := ![0, 15, 10, 5, 3, 12, 9, 6, 2, 13, 8, 7, 1, 14, 11, 4]
  invFun := ![0, 12, 8, 4, 15, 3, 7, 11, 10, 6, 2, 14, 5, 9, 13, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12]
  invFun := ![0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 10, 5, 12, 3, 6, 9, 8, 7, 2, 13, 4, 11, 14, 1]
  invFun := ![0, 15, 10, 5, 12, 3, 6, 9, 8, 7, 2, 13, 4, 11, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 3, 2, 4, 5, 7, 6, 12, 13, 15, 14, 8, 9, 11, 10]
  invFun := ![0, 1, 3, 2, 4, 5, 7, 6, 12, 13, 15, 14, 8, 9, 11, 10]
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
  toFun := ![0, 12, 4, 8, 15, 3, 11, 7, 5, 9, 1, 13, 10, 6, 14, 2]
  invFun := ![0, 10, 15, 5, 2, 8, 13, 7, 3, 9, 12, 6, 1, 11, 14, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 4, 8, 3, 15, 7, 11, 1, 13, 5, 9, 2, 14, 6, 10]
  invFun := ![0, 8, 12, 4, 2, 10, 14, 6, 3, 11, 15, 7, 1, 9, 13, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 5, 15, 2, 8, 7, 13, 1, 11, 4, 14, 3, 9, 6, 12]
  invFun := ![0, 8, 4, 12, 10, 2, 14, 6, 5, 13, 1, 9, 15, 7, 11, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 1, 2, 15, 12, 14, 13, 5, 6, 4, 7, 10, 9, 11, 8]
  invFun := ![0, 2, 3, 1, 10, 8, 9, 11, 15, 13, 12, 14, 5, 7, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 5, 15, 8, 2, 13, 7, 4, 14, 1, 11, 12, 6, 9, 3]
  invFun := ![0, 10, 5, 15, 8, 2, 13, 7, 4, 14, 1, 11, 12, 6, 9, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 8, 4, 15, 3, 7, 11, 10, 6, 2, 14, 5, 9, 13, 1]
  invFun := ![0, 15, 10, 5, 3, 12, 9, 6, 2, 13, 8, 7, 1, 14, 11, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5]
  invFun := ![0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 15, 10, 1, 4, 14, 11, 3, 6, 12, 9, 2, 7, 13, 8]
  invFun := ![0, 4, 12, 8, 5, 1, 9, 13, 15, 11, 3, 7, 10, 14, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 2, 1, 15, 12, 13, 14, 10, 9, 8, 11, 5, 6, 7, 4]
  invFun := ![0, 3, 2, 1, 15, 12, 13, 14, 10, 9, 8, 11, 5, 6, 7, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 15, 10, 4, 1, 11, 14, 12, 9, 3, 6, 8, 13, 7, 2]
  invFun := ![0, 5, 15, 10, 4, 1, 11, 14, 12, 9, 3, 6, 8, 13, 7, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 12, 4, 10, 2, 6, 14, 15, 7, 3, 11, 5, 13, 9, 1]
  invFun := ![0, 15, 5, 10, 3, 12, 6, 9, 1, 14, 4, 11, 2, 13, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 12, 4, 2, 10, 14, 6, 3, 11, 15, 7, 1, 9, 13, 5]
  invFun := ![0, 12, 4, 8, 3, 15, 7, 11, 1, 13, 5, 9, 2, 14, 6, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 3, 1, 10, 8, 9, 11, 15, 13, 12, 14, 5, 7, 6, 4]
  invFun := ![0, 3, 1, 2, 15, 12, 14, 13, 5, 6, 4, 7, 10, 9, 11, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e30 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 4, 12, 10, 2, 14, 6, 5, 13, 1, 9, 15, 7, 11, 3]
  invFun := ![0, 10, 5, 15, 2, 8, 7, 13, 1, 11, 4, 14, 3, 9, 6, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e31 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  invFun := ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e32 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 1, 3, 10, 8, 11, 9, 5, 7, 4, 6, 15, 13, 14, 12]
  invFun := ![0, 2, 1, 3, 10, 8, 11, 9, 5, 7, 4, 6, 15, 13, 14, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e33 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 12, 8, 5, 1, 9, 13, 15, 11, 3, 7, 10, 14, 6, 2]
  invFun := ![0, 5, 15, 10, 1, 4, 14, 11, 3, 6, 12, 9, 2, 7, 13, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e34 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 12, 8, 1, 5, 13, 9, 3, 7, 15, 11, 2, 6, 14, 10]
  invFun := ![0, 4, 12, 8, 1, 5, 13, 9, 3, 7, 15, 11, 2, 6, 14, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e35 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8]
  invFun := ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 4 → Equiv.Perm (Fin 16) :=
  ![g0, g1, g2, g3]
def elements : Fin 36 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35]
def next : Fin 36 → Fin 4 → Fin 36 :=
  ![![1, 2, 3, 4], ![5, 6, 7, 8], ![6, 9, 10, 11], ![7, 12, 0, 13], ![14, 11, 13, 0], ![0, 15, 16, 14], ![15, 17, 18, 19], ![16, 20, 1, 21], ![4, 19, 21, 1], ![17, 0, 12, 22], ![18, 3, 2, 23], ![24, 22, 23, 2], ![20, 10, 9, 25], ![26, 25, 4, 3], ![8, 24, 26, 5], ![2, 27, 28, 24], ![3, 29, 5, 26], ![27, 1, 20, 30], ![28, 7, 6, 31], ![11, 30, 31, 6], ![29, 18, 17, 32], ![13, 32, 8, 7], ![33, 4, 25, 9], ![34, 13, 11, 10], ![19, 33, 34, 15], ![35, 23, 22, 12], ![21, 35, 14, 16], ![9, 5, 29, 33], ![10, 16, 15, 34], ![12, 28, 27, 35], ![22, 8, 32, 17], ![23, 21, 19, 18], ![25, 31, 30, 20], ![30, 14, 35, 27], ![31, 26, 24, 28], ![32, 34, 33, 29]]
def words : Fin 36 → List (Fin 4) :=
  ![[], [0], [1], [2], [3], [0, 0], [0, 1], [0, 2], [0, 3], [1, 1], [1, 2], [1, 3], [2, 1], [2, 3], [3, 0], [0, 0, 1], [0, 0, 2], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 2, 1], [0, 2, 3], [1, 1, 3], [1, 2, 3], [1, 3, 0], [2, 1, 3], [2, 3, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 2, 1], [0, 1, 1, 3], [0, 1, 2, 3], [0, 2, 1, 3], [1, 1, 3, 0], [1, 2, 3, 0], [2, 1, 3, 0]]

def certificate : FiniteCayleyCertificate generators 36 where
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

theorem card : Nat.card R = 36 := certificate.card_closure elements_injective

end SmallAffineSoluble16Row7Order
end SymmetricSubgroupAsymptotics
