import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row8Order

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
  toFun := ![0, 3, 12, 15, 2, 1, 14, 13, 8, 11, 4, 7, 10, 9, 6, 5]
  invFun := ![0, 5, 4, 1, 10, 15, 14, 11, 8, 13, 12, 9, 2, 7, 6, 3]
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
  toFun := ![0, 3, 12, 15, 2, 1, 14, 13, 8, 11, 4, 7, 10, 9, 6, 5]
  invFun := ![0, 5, 4, 1, 10, 15, 14, 11, 8, 13, 12, 9, 2, 7, 6, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5]
  invFun := ![0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 5, 10, 3, 12, 6, 9, 1, 14, 4, 11, 2, 13, 7, 8]
  invFun := ![0, 8, 12, 4, 10, 2, 6, 14, 15, 7, 3, 11, 5, 13, 9, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 8, 10, 1, 3, 9, 11, 4, 6, 12, 14, 5, 7, 13, 15]
  invFun := ![0, 4, 1, 5, 8, 12, 9, 13, 2, 6, 3, 7, 10, 14, 11, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3]
  invFun := ![0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 3, 12, 10, 5, 9, 6, 2, 13, 1, 14, 8, 7, 11, 4]
  invFun := ![0, 10, 8, 2, 15, 5, 7, 13, 12, 6, 4, 14, 3, 9, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 4, 5, 3, 2, 7, 6, 12, 13, 8, 9, 15, 14, 11, 10]
  invFun := ![0, 1, 5, 4, 2, 3, 7, 6, 10, 11, 15, 14, 8, 9, 13, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 10, 5, 12, 3, 6, 9, 8, 7, 2, 13, 4, 11, 14, 1]
  invFun := ![0, 15, 10, 5, 12, 3, 6, 9, 8, 7, 2, 13, 4, 11, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 15, 5, 2, 8, 13, 7, 3, 9, 12, 6, 1, 11, 14, 4]
  invFun := ![0, 12, 4, 8, 15, 3, 11, 7, 5, 9, 1, 13, 10, 6, 14, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 4, 8, 15, 3, 11, 7, 5, 9, 1, 13, 10, 6, 14, 2]
  invFun := ![0, 10, 15, 5, 2, 8, 13, 7, 3, 9, 12, 6, 1, 11, 14, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 2, 8, 5, 15, 7, 13, 1, 11, 3, 9, 4, 14, 6, 12]
  invFun := ![0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 5, 15, 8, 2, 13, 7, 4, 14, 1, 11, 12, 6, 9, 3]
  invFun := ![0, 10, 5, 15, 8, 2, 13, 7, 4, 14, 1, 11, 12, 6, 9, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 15, 3, 8, 4, 7, 11, 10, 6, 5, 9, 2, 14, 13, 1]
  invFun := ![0, 15, 12, 3, 5, 10, 9, 6, 4, 11, 8, 7, 1, 14, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 1, 4, 15, 10, 14, 11, 3, 6, 2, 7, 12, 9, 13, 8]
  invFun := ![0, 2, 10, 8, 3, 1, 9, 11, 15, 13, 5, 7, 12, 14, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5]
  invFun := ![0, 12, 8, 4, 3, 15, 11, 7, 2, 14, 10, 6, 1, 13, 9, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 15, 10, 4, 1, 11, 14, 12, 9, 3, 6, 8, 13, 7, 2]
  invFun := ![0, 5, 15, 10, 4, 1, 11, 14, 12, 9, 3, 6, 8, 13, 7, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 2, 1, 15, 12, 13, 14, 10, 9, 8, 11, 5, 6, 7, 4]
  invFun := ![0, 3, 2, 1, 15, 12, 13, 14, 10, 9, 8, 11, 5, 6, 7, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 4, 1, 10, 15, 14, 11, 8, 13, 12, 9, 2, 7, 6, 3]
  invFun := ![0, 3, 12, 15, 2, 1, 14, 13, 8, 11, 4, 7, 10, 9, 6, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 12, 4, 10, 2, 6, 14, 15, 7, 3, 11, 5, 13, 9, 1]
  invFun := ![0, 15, 5, 10, 3, 12, 6, 9, 1, 14, 4, 11, 2, 13, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 10, 2, 4, 12, 14, 6, 5, 13, 15, 7, 1, 9, 11, 3]
  invFun := ![0, 12, 3, 15, 4, 8, 7, 11, 1, 13, 2, 14, 5, 9, 6, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  invFun := ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 1, 3, 10, 8, 11, 9, 5, 7, 4, 6, 15, 13, 14, 12]
  invFun := ![0, 2, 1, 3, 10, 8, 11, 9, 5, 7, 4, 6, 15, 13, 14, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 12, 3, 5, 10, 9, 6, 4, 11, 8, 7, 1, 14, 13, 2]
  invFun := ![0, 12, 15, 3, 8, 4, 7, 11, 10, 6, 5, 9, 2, 14, 13, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 5, 1, 12, 8, 9, 13, 15, 11, 10, 14, 3, 7, 6, 2]
  invFun := ![0, 3, 15, 12, 1, 2, 14, 13, 5, 6, 10, 9, 4, 7, 11, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 12, 8, 1, 5, 13, 9, 3, 7, 15, 11, 2, 6, 14, 10]
  invFun := ![0, 4, 12, 8, 1, 5, 13, 9, 3, 7, 15, 11, 2, 6, 14, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 1, 5, 8, 12, 9, 13, 2, 6, 3, 7, 10, 14, 11, 15]
  invFun := ![0, 2, 8, 10, 1, 3, 9, 11, 4, 6, 12, 14, 5, 7, 13, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8]
  invFun := ![0, 1, 3, 2, 5, 4, 6, 7, 15, 14, 12, 13, 10, 11, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e30 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 8, 2, 15, 5, 7, 13, 12, 6, 4, 14, 3, 9, 11, 1]
  invFun := ![0, 15, 3, 12, 10, 5, 9, 6, 2, 13, 1, 14, 8, 7, 11, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e31 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 5, 4, 2, 3, 7, 6, 10, 11, 15, 14, 8, 9, 13, 12]
  invFun := ![0, 1, 4, 5, 3, 2, 7, 6, 12, 13, 8, 9, 15, 14, 11, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e32 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 3, 15, 4, 8, 7, 11, 1, 13, 2, 14, 5, 9, 6, 10]
  invFun := ![0, 8, 10, 2, 4, 12, 14, 6, 5, 13, 15, 7, 1, 9, 11, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e33 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 15, 12, 1, 2, 14, 13, 5, 6, 10, 9, 4, 7, 11, 8]
  invFun := ![0, 4, 5, 1, 12, 8, 9, 13, 15, 11, 10, 14, 3, 7, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e34 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 2, 10, 12, 4, 14, 6, 3, 11, 1, 9, 15, 7, 13, 5]
  invFun := ![0, 10, 2, 8, 5, 15, 7, 13, 1, 11, 3, 9, 4, 14, 6, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e35 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 10, 8, 3, 1, 9, 11, 15, 13, 5, 7, 12, 14, 6, 4]
  invFun := ![0, 5, 1, 4, 15, 10, 14, 11, 3, 6, 2, 7, 12, 9, 13, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![g0, g1, g2]
def elements : Fin 36 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35]
def next : Fin 36 → Fin 3 → Fin 36 :=
  ![![1, 2, 3], ![4, 5, 6], ![5, 7, 8], ![8, 9, 10], ![0, 11, 9], ![11, 12, 13], ![13, 3, 14], ![12, 0, 15], ![15, 16, 17], ![16, 6, 18], ![18, 19, 20], ![2, 21, 16], ![21, 1, 22], ![22, 8, 23], ![10, 24, 25], ![3, 26, 19], ![26, 13, 27], ![27, 10, 28], ![14, 29, 30], ![29, 17, 31], ![31, 25, 0], ![7, 4, 26], ![6, 15, 24], ![17, 14, 32], ![19, 23, 33], ![33, 30, 1], ![9, 22, 29], ![23, 18, 34], ![20, 32, 2], ![24, 27, 35], ![35, 20, 4], ![28, 33, 7], ![25, 34, 5], ![32, 35, 12], ![30, 28, 11], ![34, 31, 21]]
def words : Fin 36 → List (Fin 3) :=
  ![[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [2, 1], [2, 2], [0, 0, 1], [0, 1, 1], [0, 1, 2], [0, 2, 2], [1, 1, 2], [1, 2, 1], [1, 2, 2], [2, 1, 2], [2, 2, 1], [2, 2, 2], [0, 0, 1, 1], [0, 1, 1, 2], [0, 1, 2, 2], [0, 2, 2, 1], [0, 2, 2, 2], [1, 1, 2, 1], [1, 2, 1, 2], [1, 2, 2, 2], [2, 1, 2, 1], [2, 1, 2, 2], [2, 2, 1, 2], [0, 1, 2, 2, 2], [0, 2, 2, 1, 2], [1, 2, 1, 2, 2], [2, 1, 2, 1, 2]]

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

end SmallAffineSoluble16Row8Order
end SymmetricSubgroupAsymptotics
