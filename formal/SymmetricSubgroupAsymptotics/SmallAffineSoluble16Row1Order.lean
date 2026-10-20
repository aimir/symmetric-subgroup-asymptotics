import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row1Order

def g0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]
  invFun := ![0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1]
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
  toFun := ![0, 8, 15, 7, 1, 9, 14, 6, 2, 10, 13, 5, 3, 11, 12, 4]
  invFun := ![0, 4, 8, 12, 15, 11, 7, 3, 1, 5, 9, 13, 14, 10, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 8, 12, 15, 11, 7, 3, 1, 5, 9, 13, 14, 10, 6, 2]
  invFun := ![0, 8, 15, 7, 1, 9, 14, 6, 2, 10, 13, 5, 3, 11, 12, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1]
  invFun := ![0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 1 → Equiv.Perm (Fin 16) :=
  ![g0]
def elements : Fin 5 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4]
def next : Fin 5 → Fin 1 → Fin 5 :=
  ![![1], ![2], ![3], ![4], ![0]]
def words : Fin 5 → List (Fin 1) :=
  ![[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0]]

def certificate : FiniteCayleyCertificate generators 5 where
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

theorem card : Nat.card R = 5 := certificate.card_closure elements_injective

end SmallAffineSoluble16Row1Order
end SymmetricSubgroupAsymptotics
