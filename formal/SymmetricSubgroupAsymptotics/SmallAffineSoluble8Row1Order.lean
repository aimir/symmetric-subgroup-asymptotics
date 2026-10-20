import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble8Row1Order

def g0 : Equiv.Perm (Fin 8) where
  toFun := ![0, 6, 1, 7, 2, 4, 3, 5]
  invFun := ![0, 2, 4, 6, 5, 7, 1, 3]
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
  toFun := ![0, 3, 6, 5, 1, 2, 7, 4]
  invFun := ![0, 4, 5, 1, 7, 3, 2, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 8) where
  toFun := ![0, 7, 3, 4, 6, 1, 5, 2]
  invFun := ![0, 5, 7, 2, 3, 6, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 7, 2, 3, 6, 4, 1]
  invFun := ![0, 7, 3, 4, 6, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 8) where
  toFun := ![0, 4, 5, 1, 7, 3, 2, 6]
  invFun := ![0, 3, 6, 5, 1, 2, 7, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 8) where
  toFun := ![0, 2, 4, 6, 5, 7, 1, 3]
  invFun := ![0, 6, 1, 7, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 1 → Equiv.Perm (Fin 8) :=
  ![g0]
def elements : Fin 7 → Equiv.Perm (Fin 8) :=
  ![e0, e1, e2, e3, e4, e5, e6]
def next : Fin 7 → Fin 1 → Fin 7 :=
  ![![1], ![2], ![3], ![4], ![5], ![6], ![0]]
def words : Fin 7 → List (Fin 1) :=
  ![[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]

def certificate : FiniteCayleyCertificate generators 7 where
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

theorem card : Nat.card R = 7 := certificate.card_closure elements_injective

end SmallAffineSoluble8Row1Order
end SymmetricSubgroupAsymptotics
