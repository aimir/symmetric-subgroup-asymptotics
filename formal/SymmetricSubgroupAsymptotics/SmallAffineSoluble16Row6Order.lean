import SymmetricSubgroupAsymptotics.MetacyclicSolvabilityFactories
import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SmallAffineSoluble16Row6Order

def g0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 4, 11, 2, 13, 6, 9, 8, 7, 12, 3, 10, 5, 14, 1]
  invFun := ![0, 15, 4, 11, 2, 13, 6, 9, 8, 7, 12, 3, 10, 5, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def g1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 6, 12, 1, 11, 7, 13, 4, 14, 2, 8, 5, 15, 3, 9]
  invFun := ![0, 4, 10, 14, 8, 12, 2, 6, 11, 15, 1, 5, 3, 7, 9, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e0 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 4, 11, 2, 13, 6, 9, 8, 7, 12, 3, 10, 5, 14, 1]
  invFun := ![0, 15, 4, 11, 2, 13, 6, 9, 8, 7, 12, 3, 10, 5, 14, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 6, 12, 1, 11, 7, 13, 4, 14, 2, 8, 5, 15, 3, 9]
  invFun := ![0, 4, 10, 14, 8, 12, 2, 6, 11, 15, 1, 5, 3, 7, 9, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 6, 10, 15, 3, 9, 5, 2, 14, 4, 8, 13, 1, 11, 7]
  invFun := ![0, 13, 8, 5, 10, 7, 2, 15, 11, 6, 3, 14, 1, 12, 9, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : Equiv.Perm (Fin 16) where
  toFun := ![0, 9, 1, 8, 6, 15, 7, 14, 4, 13, 5, 12, 2, 11, 3, 10]
  invFun := ![0, 2, 12, 14, 8, 10, 4, 6, 3, 1, 15, 13, 11, 9, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 7, 5, 10, 8, 13, 15, 1, 3, 6, 4, 11, 9, 12, 14]
  invFun := ![0, 8, 1, 9, 11, 3, 10, 2, 5, 13, 4, 12, 14, 6, 15, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : Equiv.Perm (Fin 16) where
  toFun := ![0, 7, 15, 8, 6, 1, 9, 14, 2, 5, 13, 10, 4, 3, 11, 12]
  invFun := ![0, 5, 8, 13, 12, 9, 4, 1, 3, 6, 11, 14, 15, 10, 7, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 9, 13, 12, 8, 5, 1, 15, 11, 6, 2, 3, 7, 10, 14]
  invFun := ![0, 7, 11, 12, 1, 6, 10, 13, 5, 2, 14, 9, 4, 3, 15, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 7, 2, 9, 12, 14, 11, 6, 3, 1, 4, 15, 10, 8, 13]
  invFun := ![0, 10, 3, 9, 11, 1, 8, 2, 14, 4, 13, 7, 5, 15, 6, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : Equiv.Perm (Fin 16) where
  toFun := ![0, 14, 10, 4, 7, 9, 13, 3, 1, 15, 11, 5, 6, 8, 12, 2]
  invFun := ![0, 8, 15, 7, 3, 11, 12, 4, 13, 5, 2, 10, 14, 6, 1, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : Equiv.Perm (Fin 16) where
  toFun := ![0, 6, 13, 11, 2, 4, 15, 9, 10, 12, 7, 1, 8, 14, 5, 3]
  invFun := ![0, 11, 4, 15, 5, 14, 1, 10, 12, 7, 8, 3, 9, 2, 13, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : Equiv.Perm (Fin 16) where
  toFun := ![0, 13, 9, 4, 7, 10, 14, 3, 6, 11, 15, 2, 1, 12, 8, 5]
  invFun := ![0, 12, 11, 7, 3, 15, 8, 4, 14, 2, 5, 9, 13, 1, 6, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : Equiv.Perm (Fin 16) where
  toFun := ![0, 14, 12, 2, 9, 7, 5, 11, 15, 1, 3, 13, 6, 8, 10, 4]
  invFun := ![0, 9, 3, 10, 15, 6, 12, 5, 13, 4, 14, 7, 2, 11, 1, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : Equiv.Perm (Fin 16) where
  toFun := ![0, 6, 5, 3, 4, 2, 1, 7, 12, 10, 9, 15, 8, 14, 13, 11]
  invFun := ![0, 6, 5, 3, 4, 2, 1, 7, 12, 10, 9, 15, 8, 14, 13, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : Equiv.Perm (Fin 16) where
  toFun := ![0, 1, 14, 15, 5, 4, 11, 10, 9, 8, 7, 6, 12, 13, 2, 3]
  invFun := ![0, 1, 14, 15, 5, 4, 11, 10, 9, 8, 7, 6, 12, 13, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : Equiv.Perm (Fin 16) where
  toFun := ![0, 11, 13, 6, 14, 5, 3, 8, 7, 12, 10, 1, 9, 2, 4, 15]
  invFun := ![0, 11, 13, 6, 14, 5, 3, 8, 7, 12, 10, 1, 9, 2, 4, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 2, 1, 13, 14, 15, 12, 10, 9, 8, 11, 7, 4, 5, 6]
  invFun := ![0, 3, 2, 1, 13, 14, 15, 12, 10, 9, 8, 11, 7, 4, 5, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : Equiv.Perm (Fin 16) where
  toFun := ![0, 15, 14, 1, 13, 2, 3, 12, 7, 8, 9, 6, 10, 5, 4, 11]
  invFun := ![0, 3, 5, 6, 14, 13, 11, 8, 9, 10, 12, 15, 7, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : Equiv.Perm (Fin 16) where
  toFun := ![0, 3, 5, 6, 14, 13, 11, 8, 9, 10, 12, 15, 7, 4, 2, 1]
  invFun := ![0, 15, 14, 1, 13, 2, 3, 12, 7, 8, 9, 6, 10, 5, 4, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : Equiv.Perm (Fin 16) where
  toFun := ![0, 11, 4, 15, 5, 14, 1, 10, 12, 7, 8, 3, 9, 2, 13, 6]
  invFun := ![0, 6, 13, 11, 2, 4, 15, 9, 10, 12, 7, 1, 8, 14, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : Equiv.Perm (Fin 16) where
  toFun := ![0, 7, 11, 12, 1, 6, 10, 13, 5, 2, 14, 9, 4, 3, 15, 8]
  invFun := ![0, 4, 9, 13, 12, 8, 5, 1, 15, 11, 6, 2, 3, 7, 10, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : Equiv.Perm (Fin 16) where
  toFun := ![0, 10, 3, 9, 11, 1, 8, 2, 14, 4, 13, 7, 5, 15, 6, 12]
  invFun := ![0, 5, 7, 2, 9, 12, 14, 11, 6, 3, 1, 4, 15, 10, 8, 13]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 15, 7, 3, 11, 12, 4, 13, 5, 2, 10, 14, 6, 1, 9]
  invFun := ![0, 14, 10, 4, 7, 9, 13, 3, 1, 15, 11, 5, 6, 8, 12, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : Equiv.Perm (Fin 16) where
  toFun := ![0, 9, 3, 10, 15, 6, 12, 5, 13, 4, 14, 7, 2, 11, 1, 8]
  invFun := ![0, 14, 12, 2, 9, 7, 5, 11, 15, 1, 3, 13, 6, 8, 10, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : Equiv.Perm (Fin 16) where
  toFun := ![0, 12, 11, 7, 3, 15, 8, 4, 14, 2, 5, 9, 13, 1, 6, 10]
  invFun := ![0, 13, 9, 4, 7, 10, 14, 3, 6, 11, 15, 2, 1, 12, 8, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : Equiv.Perm (Fin 16) where
  toFun := ![0, 8, 1, 9, 11, 3, 10, 2, 5, 13, 4, 12, 14, 6, 15, 7]
  invFun := ![0, 2, 7, 5, 10, 8, 13, 15, 1, 3, 6, 4, 11, 9, 12, 14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : Equiv.Perm (Fin 16) where
  toFun := ![0, 13, 8, 5, 10, 7, 2, 15, 11, 6, 3, 14, 1, 12, 9, 4]
  invFun := ![0, 12, 6, 10, 15, 3, 9, 5, 2, 14, 4, 8, 13, 1, 11, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : Equiv.Perm (Fin 16) where
  toFun := ![0, 2, 12, 14, 8, 10, 4, 6, 3, 1, 15, 13, 11, 9, 7, 5]
  invFun := ![0, 9, 1, 8, 6, 15, 7, 14, 4, 13, 5, 12, 2, 11, 3, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : Equiv.Perm (Fin 16) where
  toFun := ![0, 5, 8, 13, 12, 9, 4, 1, 3, 6, 11, 14, 15, 10, 7, 2]
  invFun := ![0, 7, 15, 8, 6, 1, 9, 14, 2, 5, 13, 10, 4, 3, 11, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : Equiv.Perm (Fin 16) where
  toFun := ![0, 4, 10, 14, 8, 12, 2, 6, 11, 15, 1, 5, 3, 7, 9, 13]
  invFun := ![0, 10, 6, 12, 1, 11, 7, 13, 4, 14, 2, 8, 5, 15, 3, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 2 → Equiv.Perm (Fin 16) :=
  ![g0, g1]
def elements : Fin 30 → Equiv.Perm (Fin 16) :=
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29]
def next : Fin 30 → Fin 2 → Fin 30 :=
  ![![1, 2], ![0, 3], ![4, 5], ![6, 7], ![2, 8], ![9, 10], ![3, 11], ![12, 13], ![11, 14], ![5, 15], ![16, 6], ![8, 17], ![7, 18], ![19, 4], ![18, 20], ![17, 21], ![10, 22], ![15, 23], ![14, 24], ![13, 25], ![25, 9], ![24, 26], ![23, 27], ![22, 12], ![21, 28], ![20, 29], ![29, 16], ![28, 1], ![27, 19], ![26, 0]]
def words : Fin 30 → List (Fin 2) :=
  ![[], [0], [1], [0, 1], [1, 0], [1, 1], [0, 1, 0], [0, 1, 1], [1, 0, 1], [1, 1, 0], [1, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0], [0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 1, 0], [1, 0, 1, 1, 1], [1, 1, 0, 1, 1], [1, 1, 1, 0, 1], [0, 1, 0, 1, 1, 1], [0, 1, 1, 0, 1, 1], [0, 1, 1, 1, 0, 1], [1, 1, 0, 1, 1, 1], [1, 1, 1, 0, 1, 1], [0, 1, 1, 0, 1, 1, 1], [0, 1, 1, 1, 0, 1, 1]]

def certificate : FiniteCayleyCertificate generators 30 where
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

theorem card : Nat.card R = 30 := certificate.card_closure elements_injective

theorem conjugates : g0*g1*g0⁻¹=g1^4 ∧ g0⁻¹*g1*g0=g1^4 := by
  constructor <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem soluble : IsSolvable R := by
  have hrange : Set.range generators = ({g1,g0} : Set (Equiv.Perm (Fin 16))) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [generators]
    · rintro (h | h)
      · exact ⟨1, h.symm⟩
      · exact ⟨0, h.symm⟩
  change IsSolvable (Subgroup.closure (Set.range generators))
  rw [hrange]
  exact isSolvable_closure_of_conjugate_powers g1 g0 4 4 conjugates.1 conjugates.2

end SmallAffineSoluble16Row6Order
end SymmetricSubgroupAsymptotics
