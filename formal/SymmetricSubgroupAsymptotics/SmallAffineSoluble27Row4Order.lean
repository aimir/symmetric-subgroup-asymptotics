import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble27Row4Order

def g0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 3, 12, 21, 4, 13, 22, 5, 14, 23, 6, 15, 24, 7, 16, 25, 8, 17, 26]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 9, 11, 10, 15, 17, 16, 12, 14, 13, 18, 20, 19, 24, 26, 25, 21, 23, 22]
  invFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 9, 11, 10, 15, 17, 16, 12, 14, 13, 18, 20, 19, 24, 26, 25, 21, 23, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g2 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 6, 7, 8, 3, 4, 5, 9, 10, 11, 15, 16, 17, 12, 13, 14, 18, 19, 20, 24, 25, 26, 21, 22, 23]
  invFun := ![0, 1, 2, 6, 7, 8, 3, 4, 5, 9, 10, 11, 15, 16, 17, 12, 13, 14, 18, 19, 20, 24, 25, 26, 21, 22, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 3, 12, 21, 4, 13, 22, 5, 14, 23, 6, 15, 24, 7, 16, 25, 8, 17, 26]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 9, 11, 10, 15, 17, 16, 12, 14, 13, 18, 20, 19, 24, 26, 25, 21, 23, 22]
  invFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 9, 11, 10, 15, 17, 16, 12, 14, 13, 18, 20, 19, 24, 26, 25, 21, 23, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 6, 7, 8, 3, 4, 5, 9, 10, 11, 15, 16, 17, 12, 13, 14, 18, 19, 20, 24, 25, 26, 21, 22, 23]
  invFun := ![0, 1, 2, 6, 7, 8, 3, 4, 5, 9, 10, 11, 15, 16, 17, 12, 13, 14, 18, 19, 20, 24, 25, 26, 21, 22, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 1, 4, 7, 10, 13, 16, 19, 22, 25, 2, 5, 8, 11, 14, 17, 20, 23, 26]
  invFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 3, 12, 21, 4, 13, 22, 5, 14, 23, 6, 15, 24, 7, 16, 25, 8, 17, 26]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 2, 20, 11, 1, 19, 10, 3, 21, 12, 5, 23, 14, 4, 22, 13, 6, 24, 15, 8, 26, 17, 7, 25, 16]
  invFun := ![0, 6, 3, 9, 15, 12, 18, 24, 21, 2, 8, 5, 11, 17, 14, 20, 26, 23, 1, 7, 4, 10, 16, 13, 19, 25, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 2, 11, 20, 1, 10, 19, 3, 12, 21, 5, 14, 23, 4, 13, 22, 6, 15, 24, 8, 17, 26, 7, 16, 25]
  invFun := ![0, 6, 3, 9, 15, 12, 18, 24, 21, 1, 7, 4, 10, 16, 13, 19, 25, 22, 2, 8, 5, 11, 17, 14, 20, 26, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 2, 11, 20, 1, 10, 19, 6, 15, 24, 8, 17, 26, 7, 16, 25, 3, 12, 21, 5, 14, 23, 4, 13, 22]
  invFun := ![0, 6, 3, 18, 24, 21, 9, 15, 12, 1, 7, 4, 19, 25, 22, 10, 16, 13, 2, 8, 5, 20, 26, 23, 11, 17, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 17, 16, 18, 20, 19, 21, 23, 22, 24, 26, 25]
  invFun := ![0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 17, 16, 18, 20, 19, 21, 23, 22, 24, 26, 25]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 27) where
  toFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 6, 15, 24, 7, 16, 25, 8, 17, 26, 3, 12, 21, 4, 13, 22, 5, 14, 23]
  invFun := ![0, 3, 6, 18, 21, 24, 9, 12, 15, 1, 4, 7, 19, 22, 25, 10, 13, 16, 2, 5, 8, 20, 23, 26, 11, 14, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 18, 24, 21, 9, 15, 12, 1, 7, 4, 19, 25, 22, 10, 16, 13, 2, 8, 5, 20, 26, 23, 11, 17, 14]
  invFun := ![0, 9, 18, 2, 11, 20, 1, 10, 19, 6, 15, 24, 8, 17, 26, 7, 16, 25, 3, 12, 21, 5, 14, 23, 4, 13, 22]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 18, 21, 24, 9, 12, 15, 1, 4, 7, 19, 22, 25, 10, 13, 16, 2, 5, 8, 20, 23, 26, 11, 14, 17]
  invFun := ![0, 9, 18, 1, 10, 19, 2, 11, 20, 6, 15, 24, 7, 16, 25, 8, 17, 26, 3, 12, 21, 4, 13, 22, 5, 14, 23]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 18, 21, 24, 9, 12, 15, 2, 5, 8, 20, 23, 26, 11, 14, 17, 1, 4, 7, 19, 22, 25, 10, 13, 16]
  invFun := ![0, 18, 9, 1, 19, 10, 2, 20, 11, 6, 24, 15, 7, 25, 16, 8, 26, 17, 3, 21, 12, 4, 22, 13, 5, 23, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 1, 19, 10, 2, 20, 11, 3, 21, 12, 4, 22, 13, 5, 23, 14, 6, 24, 15, 7, 25, 16, 8, 26, 17]
  invFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 27) where
  toFun := ![0, 3, 6, 9, 12, 15, 18, 21, 24, 2, 5, 8, 11, 14, 17, 20, 23, 26, 1, 4, 7, 10, 13, 16, 19, 22, 25]
  invFun := ![0, 18, 9, 1, 19, 10, 2, 20, 11, 3, 21, 12, 4, 22, 13, 5, 23, 14, 6, 24, 15, 7, 25, 16, 8, 26, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 9, 15, 12, 18, 24, 21, 2, 8, 5, 11, 17, 14, 20, 26, 23, 1, 7, 4, 10, 16, 13, 19, 25, 22]
  invFun := ![0, 18, 9, 2, 20, 11, 1, 19, 10, 3, 21, 12, 5, 23, 14, 4, 22, 13, 6, 24, 15, 8, 26, 17, 7, 25, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 1, 19, 10, 2, 20, 11, 6, 24, 15, 7, 25, 16, 8, 26, 17, 3, 21, 12, 4, 22, 13, 5, 23, 14]
  invFun := ![0, 3, 6, 18, 21, 24, 9, 12, 15, 2, 5, 8, 20, 23, 26, 11, 14, 17, 1, 4, 7, 19, 22, 25, 10, 13, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 9, 15, 12, 18, 24, 21, 1, 7, 4, 10, 16, 13, 19, 25, 22, 2, 8, 5, 11, 17, 14, 20, 26, 23]
  invFun := ![0, 9, 18, 2, 11, 20, 1, 10, 19, 3, 12, 21, 5, 14, 23, 4, 13, 22, 6, 15, 24, 8, 17, 26, 7, 16, 25]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 27) where
  toFun := ![0, 18, 9, 2, 20, 11, 1, 19, 10, 6, 24, 15, 8, 26, 17, 7, 25, 16, 3, 21, 12, 5, 23, 14, 4, 22, 13]
  invFun := ![0, 6, 3, 18, 24, 21, 9, 15, 12, 2, 8, 5, 20, 26, 23, 11, 17, 14, 1, 7, 4, 19, 25, 22, 10, 16, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 6, 7, 8, 3, 4, 5, 18, 19, 20, 24, 25, 26, 21, 22, 23, 9, 10, 11, 15, 16, 17, 12, 13, 14]
  invFun := ![0, 1, 2, 6, 7, 8, 3, 4, 5, 18, 19, 20, 24, 25, 26, 21, 22, 23, 9, 10, 11, 15, 16, 17, 12, 13, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 27) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 3, 5, 4, 6, 8, 7, 18, 20, 19, 21, 23, 22, 24, 26, 25, 9, 11, 10, 12, 14, 13, 15, 17, 16]
  invFun := ![0, 2, 1, 3, 5, 4, 6, 8, 7, 18, 20, 19, 21, 23, 22, 24, 26, 25, 9, 11, 10, 12, 14, 13, 15, 17, 16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 27) where
  toFun := ![0, 6, 3, 18, 24, 21, 9, 15, 12, 2, 8, 5, 20, 26, 23, 11, 17, 14, 1, 7, 4, 19, 25, 22, 10, 16, 13]
  invFun := ![0, 18, 9, 2, 20, 11, 1, 19, 10, 6, 24, 15, 8, 26, 17, 7, 25, 16, 3, 21, 12, 5, 23, 14, 4, 22, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 27) where
  toFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  invFun := ![0, 2, 1, 6, 8, 7, 3, 5, 4, 18, 20, 19, 24, 26, 25, 21, 23, 22, 9, 11, 10, 15, 17, 16, 12, 14, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 3 → Equiv.Perm (Fin 27) :=
  ![g0, g1, g2]
def elements : Fin 24 → Equiv.Perm (Fin 27) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23]
def next : Fin 24 → Fin 3 → Fin 24 :=
  ![![1, 2, 3], ![4, 5, 6], ![7, 0, 8], ![9, 8, 0], ![0, 10, 11], ![12, 1, 13], ![14, 13, 1], ![15, 16, 9], ![6, 3, 2], ![17, 18, 7], ![19, 4, 17], ![20, 17, 4], ![21, 15, 14], ![11, 6, 5], ![8, 22, 12], ![2, 12, 22], ![10, 7, 18], ![3, 11, 10], ![22, 9, 16], ![16, 21, 20], ![13, 23, 19], ![5, 19, 23], ![23, 14, 15], ![18, 20, 21]]
def words : Fin 24 → List (Fin 3) :=
  ![[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 0], [1, 2], [2, 0], [0, 0, 1], [0, 0, 2], [0, 1, 0], [0, 1, 2], [0, 2, 0], [1, 0, 0], [1, 0, 1], [2, 0, 0], [2, 0, 1], [0, 0, 1, 0], [0, 0, 2, 0], [0, 1, 0, 0], [0, 2, 0, 1], [0, 0, 2, 0, 1]]

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

end SmallAffineSoluble27Row4Order
end SymmetricSubgroupAsymptotics
