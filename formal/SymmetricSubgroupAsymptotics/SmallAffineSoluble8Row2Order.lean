import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble8Row2Order

def g0 : Equiv.Perm (Fin 8) where
  toFun := ![0, 6, 1, 7, 2, 4, 3, 5]
  invFun := ![0, 2, 4, 6, 5, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 8) where
  toFun := ![0, 3, 1, 2, 4, 7, 5, 6]
  invFun := ![0, 2, 3, 1, 4, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 8) where
  toFun := ![0, 6, 1, 7, 2, 4, 3, 5]
  invFun := ![0, 2, 4, 6, 5, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 8) where
  toFun := ![0, 3, 1, 2, 4, 7, 5, 6]
  invFun := ![0, 2, 3, 1, 4, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 8) where
  toFun := ![0, 3, 6, 5, 1, 2, 7, 4]
  invFun := ![0, 4, 5, 1, 7, 3, 2, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 8) where
  toFun := ![0, 7, 6, 1, 2, 5, 4, 3]
  invFun := ![0, 3, 4, 7, 6, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 3, 6, 1, 4, 2, 7]
  invFun := ![0, 4, 6, 2, 5, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 3, 1, 4, 6, 7, 5]
  invFun := ![0, 3, 1, 2, 4, 7, 5, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 8) where
  toFun := ![0, 7, 3, 4, 6, 1, 5, 2]
  invFun := ![0, 5, 7, 2, 3, 6, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 8) where
  toFun := ![0, 4, 7, 3, 6, 2, 1, 5]
  invFun := ![0, 6, 5, 3, 1, 7, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 7, 6, 2, 3, 5, 4]
  invFun := ![0, 1, 4, 5, 7, 6, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 5, 7, 3, 1, 6, 4]
  invFun := ![0, 5, 1, 4, 7, 2, 6, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 8) where
  toFun := ![0, 6, 5, 3, 1, 7, 4, 2]
  invFun := ![0, 4, 7, 3, 6, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 8) where
  toFun := ![0, 7, 2, 5, 3, 4, 1, 6]
  invFun := ![0, 6, 2, 4, 5, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 7, 2, 3, 6, 4, 1]
  invFun := ![0, 7, 3, 4, 6, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 4, 5, 7, 6, 3, 2]
  invFun := ![0, 1, 7, 6, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 8) where
  toFun := ![0, 3, 4, 7, 6, 5, 2, 1]
  invFun := ![0, 7, 6, 1, 2, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 1, 4, 7, 2, 6, 3]
  invFun := ![0, 2, 5, 7, 3, 1, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 8) where
  toFun := ![0, 6, 2, 4, 5, 3, 7, 1]
  invFun := ![0, 7, 2, 5, 3, 4, 1, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 8) where
  toFun := ![0, 4, 6, 2, 5, 1, 3, 7]
  invFun := ![0, 5, 3, 6, 1, 4, 2, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 8) where
  toFun := ![0, 4, 5, 1, 7, 3, 2, 6]
  invFun := ![0, 3, 6, 5, 1, 2, 7, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 4, 6, 5, 7, 1, 3]
  invFun := ![0, 6, 1, 7, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 8) :=
  ![g0, g1]
def elements : Fin 21 → Equiv.Perm (Fin 8) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20]
def next : Fin 21 → Fin 2 → Fin 21 :=
  ![![1, 2], ![3, 4], ![5, 6], ![7, 5], ![8, 9], ![10, 11], ![12, 0], ![13, 8], ![14, 15], ![16, 1], ![17, 12], ![18, 3], ![9, 13], ![19, 10], ![2, 16], ![6, 7], ![11, 19], ![4, 18], ![15, 20], ![20, 14], ![0, 17]]
def words : Fin 21 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 1, 0], [1, 0, 0, 0], [1, 0, 1, 0], [0, 0, 0, 0, 0], [1, 0, 1, 0, 1]]

def certificate : FiniteCayleyCertificate generators 21 where
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

abbrev R : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range generators)

theorem card : Nat.card R = 21 := certificate.card_closure elements_injective

end SmallAffineSoluble8Row2Order
end SymmetricSubgroupAsymptotics
