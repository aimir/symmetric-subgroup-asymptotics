import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row5Order

def g0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]
  invFun := ![0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 15, 11, 2, 6, 13, 9, 8, 12, 7, 3, 10, 14, 5, 1]
  invFun := ![0, 15, 4, 11, 1, 14, 5, 10, 8, 7, 12, 3, 9, 6, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]
  invFun := ![0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 15, 11, 2, 6, 13, 9, 8, 12, 7, 3, 10, 14, 5, 1]
  invFun := ![0, 15, 4, 11, 1, 14, 5, 10, 8, 7, 12, 3, 9, 6, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 15, 7, 1, 9, 14, 6, 2, 10, 13, 5, 3, 11, 12, 4]
  invFun := ![0, 4, 8, 12, 15, 11, 7, 3, 1, 5, 9, 13, 14, 10, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 8, 10, 1, 3, 9, 11, 4, 6, 12, 14, 5, 7, 13, 15]
  invFun := ![0, 4, 1, 5, 8, 12, 9, 13, 2, 6, 3, 7, 10, 14, 11, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 4, 5, 15, 14, 11, 10, 2, 3, 6, 7, 13, 12, 9, 8]
  invFun := ![0, 1, 8, 9, 2, 3, 10, 11, 15, 14, 7, 6, 13, 12, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 1, 3, 15, 13, 14, 12, 8, 10, 9, 11, 7, 5, 6, 4]
  invFun := ![0, 2, 1, 3, 15, 13, 14, 12, 8, 10, 9, 11, 7, 5, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 15, 11, 7, 3, 1, 5, 9, 13, 14, 10, 6, 2]
  invFun := ![0, 8, 15, 7, 1, 9, 14, 6, 2, 10, 13, 5, 3, 11, 12, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 2, 13, 8, 7, 10, 5, 1, 14, 3, 12, 9, 6, 11, 4]
  invFun := ![0, 8, 2, 10, 15, 7, 13, 5, 4, 12, 6, 14, 11, 3, 9, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 15, 14, 8, 9, 7, 6, 4, 5, 11, 10, 12, 13, 3, 2]
  invFun := ![0, 1, 15, 14, 8, 9, 7, 6, 4, 5, 11, 10, 12, 13, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 1, 9, 4, 12, 5, 13, 15, 7, 14, 6, 11, 3, 10, 2]
  invFun := ![0, 2, 15, 13, 4, 6, 11, 9, 1, 3, 14, 12, 5, 7, 10, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 8, 7, 4, 11, 12, 3, 2, 13, 10, 5, 6, 9, 14, 1]
  invFun := ![0, 15, 8, 7, 4, 11, 12, 3, 2, 13, 10, 5, 6, 9, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 2, 6, 1, 5, 3, 7, 15, 11, 13, 9, 14, 10, 12, 8]
  invFun := ![0, 4, 2, 6, 1, 5, 3, 7, 15, 11, 13, 9, 14, 10, 12, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 4, 11, 1, 14, 5, 10, 8, 7, 12, 3, 9, 6, 13, 2]
  invFun := ![0, 4, 15, 11, 2, 6, 13, 9, 8, 12, 7, 3, 10, 14, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1]
  invFun := ![0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  invFun := ![0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 2, 10, 15, 7, 13, 5, 4, 12, 6, 14, 11, 3, 9, 1]
  invFun := ![0, 15, 2, 13, 8, 7, 10, 5, 1, 14, 3, 12, 9, 6, 11, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 1, 5, 8, 12, 9, 13, 2, 6, 3, 7, 10, 14, 11, 15]
  invFun := ![0, 2, 8, 10, 1, 3, 9, 11, 4, 6, 12, 14, 5, 7, 13, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 8, 9, 2, 3, 10, 11, 15, 14, 7, 6, 13, 12, 5, 4]
  invFun := ![0, 1, 4, 5, 15, 14, 11, 10, 2, 3, 6, 7, 13, 12, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 15, 13, 4, 6, 11, 9, 1, 3, 14, 12, 5, 7, 10, 8]
  invFun := ![0, 8, 1, 9, 4, 12, 5, 13, 15, 7, 14, 6, 11, 3, 10, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 16) :=
  ![g0, g1]
def elements : Fin 20 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19]
def next : Fin 20 → Fin 2 → Fin 20 :=
  ![![1, 2], ![3, 4], ![5, 6], ![7, 5], ![8, 9], ![10, 11], ![12, 13], ![14, 8], ![2, 15], ![6, 16], ![4, 12], ![9, 17], ![15, 18], ![19, 0], ![0, 10], ![11, 19], ![18, 1], ![13, 3], ![17, 14], ![16, 7]]
def words : Fin 20 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1], [0, 0, 0, 0], [0, 1, 0, 1], [0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 0]]

def certificate : FiniteCayleyCertificate generators 20 where
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

theorem card : Nat.card R = 20 := certificate.card_closure elements_injective

end SmallAffineSoluble16Row5Order
end SymmetricSubgroupAsymptotics
