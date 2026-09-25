import SymmetricSubgroupAsymptotics.BinaryInvariantRegistry
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic

/-! Reversible coordinate charts make every retained binary subspace an
actual submodule. Membership and dimension are consequences of checked
linear maps; no subspace-cardinality label is trusted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- A small reversible chart of a correlated binary subspace. -/
structure BinaryCoordinateSpace (w d : ℕ) where
  inclusion : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2)
  coordinates : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2)
  left_inverse : ∀ v, coordinates (inclusion v)=v

namespace BinaryCoordinateSpace
variable {w d : ℕ} (C : BinaryCoordinateSpace w d)

def space : Submodule (ZMod 2) (Fin w → ZMod 2) := C.inclusion.range

theorem mem_iff (v : Fin w → ZMod 2) :
    v∈C.space ↔ C.inclusion (C.coordinates v)=v := by
  constructor
  · rintro ⟨a,rfl⟩
    rw [C.left_inverse]
  · intro h
    exact ⟨C.coordinates v,h⟩

instance decidableMem : DecidablePred (fun v => v∈C.space) :=
  fun v => decidable_of_iff (C.inclusion (C.coordinates v)=v) (C.mem_iff v).symm

def equiv : (Fin d → ZMod 2) ≃ₗ[ZMod 2] C.space where
  toFun v := ⟨C.inclusion v,⟨v,rfl⟩⟩
  invFun v := C.coordinates v
  left_inv := C.left_inverse
  right_inv v := Subtype.ext ((C.mem_iff v).mp v.property)
  map_add' _ _ := Subtype.ext (C.inclusion.map_add _ _)
  map_smul' _ _ := Subtype.ext (C.inclusion.map_smul _ _)

theorem finrank : Module.finrank (ZMod 2) C.space=d := by
  rw [← C.equiv.finrank_eq]
  simp

theorem card : Nat.card C.space=2^d := by
  rw [← Nat.card_congr C.equiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- Containment needs only the retained coordinate basis. -/
theorem le_of_basis_mem (W : Submodule (ZMod 2) (Fin w → ZMod 2))
    (h : ∀ i, C.inclusion (Pi.single i 1) ∈ W) : C.space≤W := by
  rintro v ⟨a,rfl⟩
  have ha : a=∑ i, a i • Pi.single i (1:ZMod 2) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  rw [ha,map_sum]
  apply W.sum_mem
  intro i _
  rw [map_smul]
  exact W.smul_mem (a i) (h i)

end BinaryCoordinateSpace

/-- The actual permutation action on binary pair coordinates. The inverse
appears because conjugation sends the old coordinate to its image. -/
def binaryPermutationRepresentation (w : ℕ) :
    Representation (ZMod 2) (Equiv.Perm (Fin w)) (Fin w → ZMod 2) where
  toFun g := {
    toFun v := v ∘ g.symm
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Checked stability produces a literal subrepresentation. -/
def BinaryCoordinateSpace.subrepresentation {w d : ℕ}
    (C : BinaryCoordinateSpace w d) (T : Subgroup (Equiv.Perm (Fin w)))
    (h : ∀ g : T, ∀ v, v∈C.space →
      binaryPermutationRepresentation w (g:Equiv.Perm (Fin w)) v∈C.space) :
    Subrepresentation ((binaryPermutationRepresentation w).comp T.subtype) where
  toSubmodule := C.space
  apply_mem_toSubmodule := h

end SymmetricSubgroupAsymptotics
