import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Actual additive upper and lower block-shear subgroups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits
variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

def upper (S : Matrix I I R) : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ where
  val := Matrix.fromBlocks 1 S 0 1
  inv := Matrix.fromBlocks 1 (-S) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

def lower (S : Matrix I I R) : (Matrix (I ⊕ I) (I ⊕ I) R)ˣ where
  val := Matrix.fromBlocks 1 0 S 1
  inv := Matrix.fromBlocks 1 0 (-S) 1
  val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem upper_add (S T : Matrix I I R) : upper (S + T) = upper S * upper T := by
  apply Units.ext
  simp [upper, Matrix.fromBlocks_multiply, add_comm]

theorem lower_add (S T : Matrix I I R) : lower (S + T) = lower S * lower T := by
  apply Units.ext
  simp [lower, Matrix.fromBlocks_multiply]

@[simp] theorem upper_zero : upper (0 : Matrix I I R) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

@[simp] theorem lower_zero : lower (0 : Matrix I I R) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

def upperParameters (H : Subgroup ((Matrix (I ⊕ I) (I ⊕ I) R)ˣ)) :
    AddSubgroup (Matrix I I R) where
  carrier := {S | upper S ∈ H}
  zero_mem' := by simp
  add_mem' := by intro S T hS hT; change upper (S + T) ∈ H; rw [upper_add]; exact H.mul_mem hS hT
  neg_mem' := by
    intro S hS
    have hi : upper (-S) = (upper S)⁻¹ := by
      apply Units.ext
      rfl
    change upper (-S) ∈ H
    rw [hi]
    exact H.inv_mem hS

def lowerParameters (H : Subgroup ((Matrix (I ⊕ I) (I ⊕ I) R)ˣ)) :
    AddSubgroup (Matrix I I R) where
  carrier := {S | lower S ∈ H}
  zero_mem' := by simp
  add_mem' := by intro S T hS hT; change lower (S + T) ∈ H; rw [lower_add]; exact H.mul_mem hS hT
  neg_mem' := by
    intro S hS
    have hi : lower (-S) = (lower S)⁻¹ := by
      apply Units.ext
      rfl
    change lower (-S) ∈ H
    rw [hi]
    exact H.inv_mem hS

end SymmetricSubgroupAsymptotics.CFSGMatrixShearUnits
