import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble27Row6Order

def g0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 17, 22, 1, 15, 23, 2, 16, 21, 3, 11, 25, 4, 9, 26, 5, 10, 24, 6, 14, 19, 7, 12, 20, 8, 13, 18]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 13, 16, 10, 22, 25, 19, 4, 7, 1, 26, 20, 23, 8, 2, 5, 17, 11, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  invFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
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
  toFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  invFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 27) where
  toFun := ![0, 24, 12, 17, 5, 20, 22, 10, 7, 1, 25, 13, 15, 3, 18, 23, 11, 8, 2, 26, 14, 16, 4, 19, 21, 9, 6]
  invFun := ![0, 9, 18, 13, 22, 4, 26, 8, 17, 25, 7, 16, 2, 11, 20, 12, 21, 3, 14, 23, 5, 24, 6, 15, 1, 10, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 27) where
  toFun := ![0, 22, 17, 2, 21, 16, 1, 23, 15, 6, 19, 14, 8, 18, 13, 7, 20, 12, 3, 25, 11, 5, 24, 10, 4, 26, 9]
  invFun := ![0, 6, 3, 18, 24, 21, 9, 15, 12, 26, 23, 20, 17, 14, 11, 8, 5, 2, 13, 10, 16, 4, 1, 7, 22, 19, 25]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 27) where
  toFun := ![0, 8, 4, 24, 23, 19, 12, 11, 16, 17, 13, 9, 5, 1, 6, 20, 25, 21, 22, 18, 26, 10, 15, 14, 7, 3, 2]
  invFun := ![0, 13, 26, 25, 2, 12, 14, 24, 1, 11, 21, 7, 6, 10, 23, 22, 8, 9, 19, 5, 15, 17, 18, 4, 3, 16, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 27) where
  toFun := ![0, 12, 24, 22, 7, 10, 17, 20, 5, 2, 14, 26, 21, 6, 9, 16, 19, 4, 1, 13, 25, 23, 8, 11, 15, 18, 3]
  invFun := ![0, 18, 9, 26, 17, 8, 13, 4, 22, 14, 5, 23, 1, 19, 10, 24, 15, 6, 25, 16, 7, 12, 3, 21, 2, 20, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 27) where
  toFun := ![0, 21, 15, 8, 20, 14, 4, 25, 10, 24, 9, 3, 23, 17, 2, 19, 13, 7, 12, 6, 18, 11, 5, 26, 16, 1, 22]
  invFun := ![0, 25, 14, 11, 6, 22, 19, 17, 3, 10, 8, 21, 18, 16, 5, 2, 24, 13, 20, 15, 4, 1, 26, 12, 9, 7, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 27) where
  toFun := ![0, 4, 8, 12, 16, 11, 24, 19, 23, 22, 26, 18, 7, 2, 3, 10, 14, 15, 17, 9, 13, 20, 21, 25, 5, 6, 1]
  invFun := ![0, 26, 13, 14, 1, 24, 25, 12, 2, 19, 15, 5, 3, 20, 16, 17, 4, 18, 11, 7, 21, 22, 9, 8, 6, 23, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 27) where
  toFun := ![0, 7, 5, 21, 19, 26, 15, 13, 11, 8, 3, 1, 20, 24, 22, 14, 9, 16, 4, 2, 6, 25, 23, 18, 10, 17, 12]
  invFun := ![0, 11, 19, 10, 18, 2, 20, 1, 9, 16, 24, 8, 26, 7, 15, 6, 17, 25, 23, 4, 12, 3, 14, 22, 13, 21, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 27) where
  toFun := ![0, 15, 21, 4, 10, 25, 8, 14, 20, 12, 18, 6, 16, 22, 1, 11, 26, 5, 24, 3, 9, 19, 7, 13, 23, 2, 17]
  invFun := ![0, 14, 25, 19, 3, 17, 11, 22, 6, 20, 4, 15, 9, 23, 7, 1, 12, 26, 10, 21, 8, 2, 13, 24, 18, 5, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 27) where
  toFun := ![0, 16, 23, 7, 14, 18, 5, 9, 25, 21, 1, 17, 19, 8, 12, 26, 3, 10, 15, 22, 2, 13, 20, 6, 11, 24, 4]
  invFun := ![0, 10, 20, 16, 26, 6, 23, 3, 13, 7, 17, 24, 14, 21, 4, 18, 1, 11, 5, 12, 22, 9, 19, 2, 25, 8, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 27) where
  toFun := ![0, 5, 7, 15, 11, 13, 21, 26, 19, 4, 6, 2, 10, 12, 17, 25, 18, 23, 8, 1, 3, 14, 16, 9, 20, 22, 24]
  invFun := ![0, 19, 11, 20, 9, 1, 10, 2, 18, 23, 12, 4, 13, 5, 21, 3, 22, 14, 16, 8, 24, 6, 25, 17, 26, 15, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 27) where
  toFun := ![0, 10, 20, 16, 26, 6, 23, 3, 13, 7, 17, 24, 14, 21, 4, 18, 1, 11, 5, 12, 22, 9, 19, 2, 25, 8, 15]
  invFun := ![0, 16, 23, 7, 14, 18, 5, 9, 25, 21, 1, 17, 19, 8, 12, 26, 3, 10, 15, 22, 2, 13, 20, 6, 11, 24, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 27) where
  toFun := ![0, 23, 16, 5, 25, 9, 7, 18, 14, 15, 2, 22, 11, 4, 24, 13, 6, 20, 21, 17, 1, 26, 10, 3, 19, 12, 8]
  invFun := ![0, 20, 10, 23, 13, 3, 16, 6, 26, 5, 22, 12, 25, 15, 8, 9, 2, 19, 7, 24, 17, 18, 11, 1, 14, 4, 21]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 27) where
  toFun := ![0, 11, 19, 10, 18, 2, 20, 1, 9, 16, 24, 8, 26, 7, 15, 6, 17, 25, 23, 4, 12, 3, 14, 22, 13, 21, 5]
  invFun := ![0, 7, 5, 21, 19, 26, 15, 13, 11, 8, 3, 1, 20, 24, 22, 14, 9, 16, 4, 2, 6, 25, 23, 18, 10, 17, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 27) where
  toFun := ![0, 20, 10, 23, 13, 3, 16, 6, 26, 5, 22, 12, 25, 15, 8, 9, 2, 19, 7, 24, 17, 18, 11, 1, 14, 4, 21]
  invFun := ![0, 23, 16, 5, 25, 9, 7, 18, 14, 15, 2, 22, 11, 4, 24, 13, 6, 20, 21, 17, 1, 26, 10, 3, 19, 12, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 27) where
  toFun := ![0, 25, 14, 11, 6, 22, 19, 17, 3, 10, 8, 21, 18, 16, 5, 2, 24, 13, 20, 15, 4, 1, 26, 12, 9, 7, 23]
  invFun := ![0, 21, 15, 8, 20, 14, 4, 25, 10, 24, 9, 3, 23, 17, 2, 19, 13, 7, 12, 6, 18, 11, 5, 26, 16, 1, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 27) where
  toFun := ![0, 19, 11, 20, 9, 1, 10, 2, 18, 23, 12, 4, 13, 5, 21, 3, 22, 14, 16, 8, 24, 6, 25, 17, 26, 15, 7]
  invFun := ![0, 5, 7, 15, 11, 13, 21, 26, 19, 4, 6, 2, 10, 12, 17, 25, 18, 23, 8, 1, 3, 14, 16, 9, 20, 22, 24]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 27) where
  toFun := ![0, 13, 26, 25, 2, 12, 14, 24, 1, 11, 21, 7, 6, 10, 23, 22, 8, 9, 19, 5, 15, 17, 18, 4, 3, 16, 20]
  invFun := ![0, 8, 4, 24, 23, 19, 12, 11, 16, 17, 13, 9, 5, 1, 6, 20, 25, 21, 22, 18, 26, 10, 15, 14, 7, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 27) where
  toFun := ![0, 14, 25, 19, 3, 17, 11, 22, 6, 20, 4, 15, 9, 23, 7, 1, 12, 26, 10, 21, 8, 2, 13, 24, 18, 5, 16]
  invFun := ![0, 15, 21, 4, 10, 25, 8, 14, 20, 12, 18, 6, 16, 22, 1, 11, 26, 5, 24, 3, 9, 19, 7, 13, 23, 2, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 13, 22, 4, 26, 8, 17, 25, 7, 16, 2, 11, 20, 12, 21, 3, 14, 23, 5, 24, 6, 15, 1, 10, 19]
  invFun := ![0, 24, 12, 17, 5, 20, 22, 10, 7, 1, 25, 13, 15, 3, 18, 23, 11, 8, 2, 26, 14, 16, 4, 19, 21, 9, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 14, 1, 24, 25, 12, 2, 19, 15, 5, 3, 20, 16, 17, 4, 18, 11, 7, 21, 22, 9, 8, 6, 23, 10]
  invFun := ![0, 4, 8, 12, 16, 11, 24, 19, 23, 22, 26, 18, 7, 2, 3, 10, 14, 15, 17, 9, 13, 20, 21, 25, 5, 6, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 13, 16, 10, 22, 25, 19, 4, 7, 1, 26, 20, 23, 8, 2, 5, 17, 11, 14]
  invFun := ![0, 17, 22, 1, 15, 23, 2, 16, 21, 3, 11, 25, 4, 9, 26, 5, 10, 24, 6, 14, 19, 7, 12, 20, 8, 13, 18]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 26, 17, 8, 13, 4, 22, 14, 5, 23, 1, 19, 10, 24, 15, 6, 25, 16, 7, 12, 3, 21, 2, 20, 11]
  invFun := ![0, 12, 24, 22, 7, 10, 17, 20, 5, 2, 14, 26, 21, 6, 9, 16, 19, 4, 1, 13, 25, 23, 8, 11, 15, 18, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 18, 24, 21, 9, 15, 12, 26, 23, 20, 17, 14, 11, 8, 5, 2, 13, 10, 16, 4, 1, 7, 22, 19, 25]
  invFun := ![0, 22, 17, 2, 21, 16, 1, 23, 15, 6, 19, 14, 8, 18, 13, 7, 20, 12, 3, 25, 11, 5, 24, 10, 4, 26, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 27) :=
  ![g0, g1]
def elements : Fin 26 → Equiv.Perm (Fin 27) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25]
def next : Fin 26 → Fin 2 → Fin 26 :=
  ![![1, 2], ![3, 4], ![4, 0], ![5, 6], ![6, 1], ![7, 8], ![8, 3], ![9, 10], ![10, 5], ![11, 12], ![12, 7], ![13, 14], ![14, 9], ![15, 16], ![16, 11], ![17, 18], ![18, 13], ![19, 20], ![20, 15], ![21, 22], ![22, 17], ![23, 24], ![24, 19], ![0, 25], ![25, 21], ![2, 23]]
def words : Fin 26 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [0, 0, 0], [0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def certificate : FiniteCayleyCertificate generators 26 where
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

theorem card : Nat.card R = 26 := certificate.card_closure elements_injective

end SmallAffineSoluble27Row6Order
end SymmetricSubgroupAsymptotics
