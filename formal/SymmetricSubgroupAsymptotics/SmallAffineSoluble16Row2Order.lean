import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row2Order

def g0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 15, 7, 2, 10, 13, 5, 4, 12, 11, 3, 6, 14, 9, 1]
  invFun := ![0, 15, 4, 11, 8, 7, 12, 3, 1, 14, 5, 10, 9, 6, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2]
  invFun := ![0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 15, 7, 2, 10, 13, 5, 4, 12, 11, 3, 6, 14, 9, 1]
  invFun := ![0, 15, 4, 11, 8, 7, 12, 3, 1, 14, 5, 10, 9, 6, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2]
  invFun := ![0, 4, 15, 11, 1, 5, 14, 10, 8, 12, 7, 3, 9, 13, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 1, 5, 15, 11, 14, 10, 2, 6, 3, 7, 13, 9, 12, 8]
  invFun := ![0, 2, 8, 10, 1, 3, 9, 11, 15, 13, 7, 5, 14, 12, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]
  invFun := ![0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 2, 10, 15, 7, 13, 5, 1, 9, 3, 11, 14, 6, 12, 4]
  invFun := ![0, 8, 2, 10, 15, 7, 13, 5, 1, 9, 3, 11, 14, 6, 12, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 8, 10, 1, 3, 9, 11, 15, 13, 7, 5, 14, 12, 6, 4]
  invFun := ![0, 4, 1, 5, 15, 11, 14, 10, 2, 6, 3, 7, 13, 9, 12, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 8, 7, 4, 11, 12, 3, 2, 13, 10, 5, 6, 9, 14, 1]
  invFun := ![0, 15, 8, 7, 4, 11, 12, 3, 2, 13, 10, 5, 6, 9, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 4, 5, 2, 3, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]
  invFun := ![0, 1, 4, 5, 2, 3, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 4, 11, 8, 7, 12, 3, 1, 14, 5, 10, 9, 6, 13, 2]
  invFun := ![0, 8, 15, 7, 2, 10, 13, 5, 4, 12, 11, 3, 6, 14, 9, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 16) :=
  ![g0, g1]
def elements : Fin 10 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
def next : Fin 10 → Fin 2 → Fin 10 :=
  ![![1, 2], ![3, 4], ![5, 0], ![6, 7], ![2, 1], ![8, 9], ![9, 8], ![4, 3], ![7, 6], ![0, 5]]
def words : Fin 10 → List (Fin 2) :=
  ![[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1]]

def certificate : FiniteCayleyCertificate generators 10 where
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

theorem card : Nat.card R = 10 := certificate.card_closure elements_injective

end SmallAffineSoluble16Row2Order
end SymmetricSubgroupAsymptotics
