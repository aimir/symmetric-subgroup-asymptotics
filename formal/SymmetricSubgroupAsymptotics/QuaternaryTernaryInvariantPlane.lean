import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! The order-three augmentation plane over `ZMod 4` has the invariant
submodule chain `0 ≤ 2V ≤ V`.  The proof uses the determinant of the two
columns `x, cycle x`; only scalar identities over `ZMod 4` are decided.
In particular this is not an elementary-abelian or semisimplicity argument. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics
namespace QuaternaryTernaryInvariantPlane

abbrev Scalar := ZMod 4
abbrev Plane := Fin 2 → Scalar

def cycle : Plane ≃ₗ[Scalar] Plane where
  toFun x := ![-x 0 - x 1, x 0]
  invFun x := ![x 1, -x 0 - x 1]
  left_inv x := by ext i; fin_cases i <;> simp <;> ring
  right_inv x := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

theorem cycle_cube : cycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  change cycle (cycle (cycle x)) = x
  ext i
  fin_cases i <;> simp [cycle] <;> ring

/-- The middle term of the invariant-submodule chain, equal to `2V`. -/
def doubleTorsion : Submodule Scalar Plane where
  carrier := {x | (2 : Scalar) • x = 0}
  zero_mem' := by simp
  add_mem' hx hy := by simp only [Set.mem_setOf_eq] at *; rw [smul_add, hx, hy, add_zero]
  smul_mem' a x hx := by
    change (2 : Scalar) • (a • x) = 0
    rw [smul_comm, hx, smul_zero]

theorem doubleTorsion_cycle (x : Plane) (hx : x ∈ doubleTorsion) :
    cycle x ∈ doubleTorsion := by
  change (2 : Scalar) • cycle x = 0
  rw [← map_smul, show (2 : Scalar) • x = 0 from hx, map_zero]

def norm (x : Plane) : Scalar := x 0 * x 0 + x 0 * x 1 + x 1 * x 1

theorem norm_square_of_not_doubleTorsion (x : Plane) (hx : x ∉ doubleTorsion) :
    norm x * norm x = 1 := by
  have hscalar : ∀ a b : Scalar, ¬ (2 * a = 0 ∧ 2 * b = 0) →
      (a * a + a * b + b * b) * (a * a + a * b + b * b) = 1 := by
    decide +kernel
  apply hscalar
  intro h
  apply hx
  change (2 : Scalar) • x = 0
  ext i
  fin_cases i
  · exact h.1
  · exact h.2

theorem determinant_identity (x y : Plane) :
    (norm x * (x 0 * y 0 + (x 0 + x 1) * y 1)) • x +
      (norm x * (-x 1 * y 0 + x 0 * y 1)) • cycle x =
        (norm x * norm x) • y := by
  ext i
  fin_cases i <;> simp [cycle, norm] <;> ring

theorem eq_top_of_primitive (W : Submodule Scalar Plane)
    (hcycle : ∀ x ∈ W, cycle x ∈ W)
    (x : Plane) (hx : x ∈ W) (hprimitive : x ∉ doubleTorsion) : W = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  have h := W.add_mem
    (W.smul_mem (norm x * (x 0 * y 0 + (x 0 + x 1) * y 1)) hx)
    (W.smul_mem (norm x * (-x 1 * y 0 + x 0 * y 1)) (hcycle x hx))
  rw [determinant_identity, norm_square_of_not_doubleTorsion x hprimitive, one_smul] at h
  exact h

def doubledFirst : Plane := ![2, 0]
def doubledSecond : Plane := ![0, 2]

theorem doubled_orbit (x : Plane) (hx : x ∈ doubleTorsion) (hne : x ≠ 0) :
    x = doubledFirst ∨ cycle x = doubledFirst ∨ cycle (cycle x) = doubledFirst := by
  have h : ∀ x : Plane, (2 : Scalar) • x = 0 → x ≠ 0 →
      x = doubledFirst ∨ cycle x = doubledFirst ∨ cycle (cycle x) = doubledFirst := by
    decide +kernel
  exact h x hx hne

theorem doubledSecond_eq : doubledSecond = doubledFirst + cycle doubledFirst := by
  decide +kernel

theorem doubleTorsion_coordinates (x : Plane) (hx : x ∈ doubleTorsion) :
    ∃ a b : Scalar, a • doubledFirst + b • doubledSecond = x := by
  have h : ∀ x : Plane, (2 : Scalar) • x = 0 →
      ∃ a b : Scalar, a • doubledFirst + b • doubledSecond = x := by
    decide +kernel
  exact h x hx

theorem eq_doubleTorsion_of_nonzero (W : Submodule Scalar Plane)
    (hcycle : ∀ x ∈ W, cycle x ∈ W) (hW : W ≤ doubleTorsion)
    (x : Plane) (hx : x ∈ W) (hne : x ≠ 0) : W = doubleTorsion := by
  have he₀ : doubledFirst ∈ W := by
    rcases doubled_orbit x (hW hx) hne with h | h | h
    · exact h ▸ hx
    · exact h ▸ hcycle x hx
    · exact h ▸ hcycle (cycle x) (hcycle x hx)
  have he₁ : doubledSecond ∈ W := by
    rw [doubledSecond_eq]
    exact W.add_mem he₀ (hcycle doubledFirst he₀)
  apply le_antisymm hW
  intro y hy
  obtain ⟨a, b, hab⟩ := doubleTorsion_coordinates y hy
  rw [← hab]
  exact W.add_mem (W.smul_mem a he₀) (W.smul_mem b he₁)

theorem invariant_submodule_cases (W : Submodule Scalar Plane)
    (hcycle : ∀ x ∈ W, cycle x ∈ W) :
    W = ⊥ ∨ W = doubleTorsion ∨ W = ⊤ := by
  classical
  by_cases hW : W ≤ doubleTorsion
  · by_cases hzero : ∀ x ∈ W, x = 0
    · left
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (Submodule.mem_bot (R := Scalar)).mpr (hzero x hx)
    · push_neg at hzero
      obtain ⟨x, hx, hne⟩ := hzero
      exact Or.inr (Or.inl (eq_doubleTorsion_of_nonzero W hcycle hW x hx hne))
  · obtain ⟨x, hx, hprimitive⟩ := Set.not_subset.mp hW
    exact Or.inr (Or.inr (eq_top_of_primitive W hcycle x hx hprimitive))

theorem invariant_submodule_total (W U : Submodule Scalar Plane)
    (hW : ∀ x ∈ W, cycle x ∈ W) (hU : ∀ x ∈ U, cycle x ∈ U) :
    W ≤ U ∨ U ≤ W := by
  rcases invariant_submodule_cases W hW with rfl | rfl | rfl
  · exact Or.inl bot_le
  · rcases invariant_submodule_cases U hU with rfl | rfl | rfl
    · exact Or.inr bot_le
    · exact Or.inl le_rfl
    · exact Or.inl le_top
  · exact Or.inr le_top

end QuaternaryTernaryInvariantPlane
end SymmetricSubgroupAsymptotics
