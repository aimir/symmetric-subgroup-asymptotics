import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row4Order

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
  toFun := ![0, 15, 5, 10, 12, 3, 9, 6, 4, 11, 1, 14, 8, 7, 13, 2]
  invFun := ![0, 10, 15, 5, 8, 2, 7, 13, 12, 6, 3, 9, 4, 14, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3]
  invFun := ![0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]
  invFun := ![0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12]
  invFun := ![0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 15, 5, 2, 8, 13, 7, 3, 9, 12, 6, 1, 11, 14, 4]
  invFun := ![0, 12, 4, 8, 15, 3, 11, 7, 5, 9, 1, 13, 10, 6, 14, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 15, 5, 8, 2, 7, 13, 12, 6, 3, 9, 4, 14, 11, 1]
  invFun := ![0, 15, 5, 10, 12, 3, 9, 6, 4, 11, 1, 14, 8, 7, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 4, 8, 15, 3, 11, 7, 5, 9, 1, 13, 10, 6, 14, 2]
  invFun := ![0, 10, 15, 5, 2, 8, 13, 7, 3, 9, 12, 6, 1, 11, 14, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 4, 8, 3, 15, 7, 11, 1, 13, 5, 9, 2, 14, 6, 10]
  invFun := ![0, 8, 12, 4, 2, 10, 14, 6, 3, 11, 15, 7, 1, 9, 13, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 1, 2, 15, 12, 14, 13, 5, 6, 4, 7, 10, 9, 11, 8]
  invFun := ![0, 2, 3, 1, 10, 8, 9, 11, 15, 13, 12, 14, 5, 7, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 12, 4, 10, 2, 6, 14, 15, 7, 3, 11, 5, 13, 9, 1]
  invFun := ![0, 15, 5, 10, 3, 12, 6, 9, 1, 14, 4, 11, 2, 13, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 12, 4, 2, 10, 14, 6, 3, 11, 15, 7, 1, 9, 13, 5]
  invFun := ![0, 12, 4, 8, 3, 15, 7, 11, 1, 13, 5, 9, 2, 14, 6, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 3, 1, 10, 8, 9, 11, 15, 13, 12, 14, 5, 7, 6, 4]
  invFun := ![0, 3, 1, 2, 15, 12, 14, 13, 5, 6, 4, 7, 10, 9, 11, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 3 → Equiv.Perm (Fin 16) :=
  ![g0, g1, g2]
def elements : Fin 18 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]
def next : Fin 18 → Fin 3 → Fin 18 :=
  ![![1, 2, 3], ![4, 5, 6], ![5, 7, 8], ![6, 9, 0], ![0, 10, 11], ![10, 12, 13], ![11, 14, 1], ![12, 0, 9], ![13, 3, 2], ![14, 8, 7], ![2, 15, 16], ![3, 17, 4], ![15, 1, 14], ![16, 6, 5], ![17, 13, 12], ![7, 4, 17], ![8, 11, 10], ![9, 16, 15]]
def words : Fin 18 → List (Fin 3) :=
  ![[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [2, 1], [0, 0, 1], [0, 0, 2], [0, 1, 1], [0, 1, 2], [0, 2, 1], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 2, 1]]

def certificate : FiniteCayleyCertificate generators 18 where
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

theorem card : Nat.card R = 18 := certificate.card_closure elements_injective

end SmallAffineSoluble16Row4Order
end SymmetricSubgroupAsymptotics
