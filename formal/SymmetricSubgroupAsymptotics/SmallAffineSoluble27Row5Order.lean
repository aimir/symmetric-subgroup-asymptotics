import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble27Row5Order

def g0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 1, 24, 14, 2, 25, 12, 9, 8, 22, 10, 6, 23, 11, 7, 21, 18, 17, 4, 19, 15, 5, 20, 16, 3]
  invFun := ![0, 3, 6, 26, 20, 23, 13, 16, 10, 9, 12, 15, 8, 2, 5, 22, 25, 19, 18, 21, 24, 17, 11, 14, 4, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 1, 24, 14, 2, 25, 12, 3, 20, 16, 4, 18, 17, 5, 19, 15, 6, 23, 10, 7, 21, 11, 8, 22, 9]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 26, 20, 23, 8, 2, 5, 17, 11, 14, 13, 16, 10, 22, 25, 19, 4, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 1, 24, 14, 2, 25, 12, 9, 8, 22, 10, 6, 23, 11, 7, 21, 18, 17, 4, 19, 15, 5, 20, 16, 3]
  invFun := ![0, 3, 6, 26, 20, 23, 13, 16, 10, 9, 12, 15, 8, 2, 5, 22, 25, 19, 18, 21, 24, 17, 11, 14, 4, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 1, 24, 14, 2, 25, 12, 3, 20, 16, 4, 18, 17, 5, 19, 15, 6, 23, 10, 7, 21, 11, 8, 22, 9]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 26, 20, 23, 8, 2, 5, 17, 11, 14, 13, 16, 10, 22, 25, 19, 4, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 26, 20, 23, 13, 16, 10, 9, 12, 15, 8, 2, 5, 22, 25, 19, 18, 21, 24, 17, 11, 14, 4, 7, 1]
  invFun := ![0, 26, 13, 1, 24, 14, 2, 25, 12, 9, 8, 22, 10, 6, 23, 11, 7, 21, 18, 17, 4, 19, 15, 5, 20, 16, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 26, 20, 23, 13, 16, 10, 1, 4, 7, 24, 18, 21, 14, 17, 11, 2, 5, 8, 25, 19, 22, 12, 15, 9]
  invFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 26, 8, 17, 24, 6, 15, 25, 7, 16, 13, 22, 4, 14, 23, 5, 12, 21, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 26, 8, 17, 13, 22, 4, 3, 12, 21, 20, 2, 11, 16, 25, 7, 6, 15, 24, 23, 5, 14, 10, 19, 1]
  invFun := ![0, 26, 13, 9, 8, 22, 18, 17, 4, 1, 24, 14, 10, 6, 23, 19, 15, 5, 2, 25, 12, 11, 7, 21, 20, 16, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 26, 8, 17, 13, 22, 4, 1, 10, 19, 24, 6, 15, 14, 23, 5, 2, 11, 20, 25, 7, 16, 12, 21, 3]
  invFun := ![0, 9, 18, 26, 8, 17, 13, 22, 4, 1, 10, 19, 24, 6, 15, 14, 23, 5, 2, 11, 20, 25, 7, 16, 12, 21, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 26, 24, 25, 20, 18, 19, 23, 21, 22, 13, 14, 12, 16, 17, 15, 10, 11, 9]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 26, 24, 25, 20, 18, 19, 23, 21, 22, 13, 14, 12, 16, 17, 15, 10, 11, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 3, 12, 21, 6, 15, 24, 1, 10, 19, 4, 13, 22, 7, 16, 25, 2, 11, 20, 5, 14, 23, 8, 17, 26]
  invFun := ![0, 9, 18, 3, 12, 21, 6, 15, 24, 1, 10, 19, 4, 13, 22, 7, 16, 25, 2, 11, 20, 5, 14, 23, 8, 17, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 3, 12, 21, 6, 15, 24, 26, 8, 17, 20, 2, 11, 23, 5, 14, 13, 22, 4, 16, 25, 7, 10, 19, 1]
  invFun := ![0, 26, 13, 3, 20, 16, 6, 23, 10, 1, 24, 14, 4, 18, 17, 7, 21, 11, 2, 25, 12, 5, 19, 15, 8, 22, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 9, 10, 11, 18, 19, 20, 3, 4, 5, 12, 13, 14, 21, 22, 23, 6, 7, 8, 15, 16, 17, 24, 25, 26]
  invFun := ![0, 1, 2, 9, 10, 11, 18, 19, 20, 3, 4, 5, 12, 13, 14, 21, 22, 23, 6, 7, 8, 15, 16, 17, 24, 25, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 9, 10, 11, 18, 19, 20, 26, 24, 25, 8, 6, 7, 17, 15, 16, 13, 14, 12, 22, 23, 21, 4, 5, 3]
  invFun := ![0, 1, 2, 26, 24, 25, 13, 14, 12, 3, 4, 5, 20, 18, 19, 16, 17, 15, 6, 7, 8, 23, 21, 22, 10, 11, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26]
  invFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 3, 12, 21, 4, 13, 22, 5, 14, 23, 6, 15, 24, 7, 16, 25, 8, 17, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 26, 20, 23, 8, 2, 5, 17, 11, 14, 13, 16, 10, 22, 25, 19, 4, 7, 1]
  invFun := ![0, 26, 13, 1, 24, 14, 2, 25, 12, 3, 20, 16, 4, 18, 17, 5, 19, 15, 6, 23, 10, 7, 21, 11, 8, 22, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 26, 8, 17, 24, 6, 15, 25, 7, 16, 13, 22, 4, 14, 23, 5, 12, 21, 3]
  invFun := ![0, 3, 6, 26, 20, 23, 13, 16, 10, 1, 4, 7, 24, 18, 21, 14, 17, 11, 2, 5, 8, 25, 19, 22, 12, 15, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 3, 12, 21, 4, 13, 22, 5, 14, 23, 6, 15, 24, 7, 16, 25, 8, 17, 26]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 9, 8, 22, 18, 17, 4, 1, 24, 14, 10, 6, 23, 19, 15, 5, 2, 25, 12, 11, 7, 21, 20, 16, 3]
  invFun := ![0, 9, 18, 26, 8, 17, 13, 22, 4, 3, 12, 21, 20, 2, 11, 16, 25, 7, 6, 15, 24, 23, 5, 14, 10, 19, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 9, 8, 22, 18, 17, 4, 3, 20, 16, 12, 2, 25, 21, 11, 7, 6, 23, 10, 15, 5, 19, 24, 14, 1]
  invFun := ![0, 26, 13, 9, 8, 22, 18, 17, 4, 3, 20, 16, 12, 2, 25, 21, 11, 7, 6, 23, 10, 15, 5, 19, 24, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 26, 20, 23, 24, 18, 21, 25, 19, 22, 13, 16, 10, 14, 17, 11, 12, 15, 9]
  invFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 26, 20, 23, 24, 18, 21, 25, 19, 22, 13, 16, 10, 14, 17, 11, 12, 15, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 9, 12, 15, 10, 13, 16, 11, 14, 17, 18, 21, 24, 19, 22, 25, 20, 23, 26]
  invFun := ![0, 3, 6, 1, 4, 7, 2, 5, 8, 9, 12, 15, 10, 13, 16, 11, 14, 17, 18, 21, 24, 19, 22, 25, 20, 23, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 3, 20, 16, 6, 23, 10, 1, 24, 14, 4, 18, 17, 7, 21, 11, 2, 25, 12, 5, 19, 15, 8, 22, 9]
  invFun := ![0, 9, 18, 3, 12, 21, 6, 15, 24, 26, 8, 17, 20, 2, 11, 23, 5, 14, 13, 22, 4, 16, 25, 7, 10, 19, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 27) where
  toFun := ![0, 26, 13, 3, 20, 16, 6, 23, 10, 9, 8, 22, 12, 2, 25, 15, 5, 19, 18, 17, 4, 21, 11, 7, 24, 14, 1]
  invFun := ![0, 26, 13, 3, 20, 16, 6, 23, 10, 9, 8, 22, 12, 2, 25, 15, 5, 19, 18, 17, 4, 21, 11, 7, 24, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 26, 24, 25, 13, 14, 12, 3, 4, 5, 20, 18, 19, 16, 17, 15, 6, 7, 8, 23, 21, 22, 10, 11, 9]
  invFun := ![0, 1, 2, 9, 10, 11, 18, 19, 20, 26, 24, 25, 8, 6, 7, 17, 15, 16, 13, 14, 12, 22, 23, 21, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 26, 24, 25, 13, 14, 12, 9, 10, 11, 8, 6, 7, 22, 23, 21, 18, 19, 20, 17, 15, 16, 4, 5, 3]
  invFun := ![0, 1, 2, 26, 24, 25, 13, 14, 12, 9, 10, 11, 8, 6, 7, 22, 23, 21, 18, 19, 20, 17, 15, 16, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 27) :=
  ![g0, g1]
def elements : Fin 24 → Equiv.Perm (Fin 27) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23]
def next : Fin 24 → Fin 2 → Fin 24 :=
  ![![1, 2], ![3, 4], ![5, 6], ![0, 7], ![8, 9], ![10, 11], ![12, 13], ![14, 15], ![16, 17], ![11, 10], ![2, 1], ![18, 19], ![20, 21], ![7, 0], ![13, 12], ![17, 16], ![4, 3], ![22, 23], ![9, 8], ![21, 20], ![6, 5], ![23, 22], ![15, 14], ![19, 18]]
def words : Fin 24 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 0, 1], [1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0], [1, 1, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1]]

def certificate : FiniteCayleyCertificate generators 24 where
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

theorem card : Nat.card R = 24 := certificate.card_closure elements_injective

end SmallAffineSoluble27Row5Order
end SymmetricSubgroupAsymptotics
