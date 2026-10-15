import SymmetricSubgroupAsymptotics.QuaternaryTernaryInvariantPlane
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! One fixed `C4` coordinate and the ternary augmentation plane retain
one generator for every invariant submodule. Averaging separates the two
types, so pairing their generators costs no additional position. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace QuaternaryTernaryCyclicSubmodules

open QuaternaryTernaryInvariantPlane

abbrev Coordinates := Scalar × Plane

def fullCycle : Coordinates ≃ₗ[Scalar] Coordinates :=
  (LinearEquiv.refl Scalar Scalar).prodCongr cycle

theorem fullCycle_cube : fullCycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · rfl
  · exact congrArg (fun f : Plane ≃ₗ[Scalar] Plane => f x.2) cycle_cube

def fixedPart (W : Submodule Scalar Coordinates) : Submodule Scalar Scalar where
  carrier := {a | (a, 0) ∈ W}
  zero_mem' := W.zero_mem
  add_mem' ha hb := by simpa using W.add_mem ha hb
  smul_mem' a b hb := by simpa using W.smul_mem a hb

def planePart (W : Submodule Scalar Coordinates) : Submodule Scalar Plane where
  carrier := {x | (0, x) ∈ W}
  zero_mem' := W.zero_mem
  add_mem' hx hy := by simpa using W.add_mem hx hy
  smul_mem' a x hx := by simpa using W.smul_mem a hx

theorem fixed_mem (W : Submodule Scalar Coordinates)
    (hW : ∀ x ∈ W, fullCycle x ∈ W) (x : Coordinates) (hx : x ∈ W) :
    (x.1, 0) ∈ W := by
  have h := W.smul_mem (3 : Scalar)
    (W.add_mem (W.add_mem hx (hW x hx)) (hW (fullCycle x) (hW x hx)))
  have hid : (3 : Scalar) • (x + fullCycle x + fullCycle (fullCycle x)) = (x.1, 0) := by
    apply Prod.ext
    · change (3 : Scalar) * (x.1 + x.1 + x.1) = x.1
      ring_nf
      simp only [show (9 : Scalar) = 1 from by decide +kernel, mul_one]
    · change (3 : Scalar) • (x.2 + cycle x.2 + cycle (cycle x.2)) = 0
      ext i
      fin_cases i
      · change (3 : Scalar) *
          (x.2 0 + (-x.2 0 - x.2 1) + (-(-x.2 0 - x.2 1) - x.2 0)) = 0
        ring
      · change (3 : Scalar) * (x.2 1 + x.2 0 + (-x.2 0 - x.2 1)) = 0
        ring
  exact hid ▸ h

theorem plane_mem (W : Submodule Scalar Coordinates)
    (hW : ∀ x ∈ W, fullCycle x ∈ W) (x : Coordinates) (hx : x ∈ W) :
    (0, x.2) ∈ W := by
  have h := W.sub_mem hx (fixed_mem W hW x hx)
  have hid : x - (x.1, (0 : Plane)) = (0, x.2) := by
    apply Prod.ext
    · exact sub_self x.1
    · exact sub_zero x.2
  exact hid ▸ h

theorem planePart_cycle (W : Submodule Scalar Coordinates)
    (hW : ∀ x ∈ W, fullCycle x ∈ W) :
    ∀ x ∈ planePart W, cycle x ∈ planePart W := by
  intro x hx
  exact hW (0, x) hx

theorem scalar_submodule_cyclic (I : Submodule Scalar Scalar) :
    ∃ a ∈ I, ∀ b ∈ I, ∃ c : Scalar, c • a = b := by
  obtain ⟨a, ha⟩ := IsAddCyclic.exists_generator (α := I.toAddSubgroup)
  refine ⟨a.1, a.2, ?_⟩
  intro b hb
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (ha ⟨b, hb⟩)
  refine ⟨(n : Scalar), ?_⟩
  rw [Int.cast_smul_eq_zsmul]
  exact congrArg Subtype.val hn

theorem plane_submodule_cyclic (W : Submodule Scalar Plane)
    (hW : ∀ x ∈ W, cycle x ∈ W) :
    ∃ x ∈ W, ∀ y ∈ W, ∃ a b : Scalar, a • x + b • cycle x = y := by
  rcases invariant_submodule_cases W hW with rfl | rfl | rfl
  · refine ⟨0, by simp, ?_⟩
    intro y hy
    have hyzero : y = 0 := (Submodule.mem_bot (R := Scalar)).mp hy
    refine ⟨0, 0, ?_⟩
    simp [hyzero]
  · refine ⟨doubledFirst, ?_, ?_⟩
    · change (2 : Scalar) • doubledFirst = 0
      decide +kernel
    · intro y hy
      obtain ⟨a, b, hab⟩ := doubleTorsion_coordinates y hy
      refine ⟨a + b, b, ?_⟩
      calc
        (a + b) • doubledFirst + b • cycle doubledFirst =
            a • doubledFirst + b • doubledSecond := by
          rw [doubledSecond_eq, add_smul, smul_add, add_assoc]
        _ = y := hab
  · refine ⟨![1, 0], Submodule.mem_top, ?_⟩
    intro y _
    refine ⟨y 0 + y 1, y 1, ?_⟩
    ext i
    fin_cases i <;> simp [cycle] <;> ring

/-- A vector generates the invariant submodule if every invariant
submodule containing that vector contains the original submodule. This
form interfaces directly with the actual ambient normal closure. -/
theorem exists_cyclic_vector (W : Submodule Scalar Coordinates)
    (hW : ∀ x ∈ W, fullCycle x ∈ W) :
    ∃ v ∈ W, ∀ L : Submodule Scalar Coordinates,
      (∀ x ∈ L, fullCycle x ∈ L) → v ∈ L → W ≤ L := by
  obtain ⟨a, ha, hagen⟩ := scalar_submodule_cyclic (fixedPart W)
  obtain ⟨x, hx, hxgen⟩ := plane_submodule_cyclic (planePart W) (planePart_cycle W hW)
  refine ⟨(a, x), ?_, ?_⟩
  · have h := W.add_mem ha hx
    simpa using h
  · intro L hL hv y hy
    have haL : (a, 0) ∈ L := fixed_mem L hL (a, x) hv
    have hxL : (0, x) ∈ L := plane_mem L hL (a, x) hv
    have hcxL : (0, cycle x) ∈ L := hL (0, x) hxL
    obtain ⟨b, hb⟩ := hagen y.1 (fixed_mem W hW y hy)
    obtain ⟨c, d, hcd⟩ := hxgen y.2 (plane_mem W hW y hy)
    have h := L.add_mem (L.smul_mem b haL)
      (L.add_mem (L.smul_mem c hxL) (L.smul_mem d hcxL))
    have hid : b • (a, (0 : Plane)) + (c • ((0 : Scalar), x) + d • (0, cycle x)) = y := by
      apply Prod.ext
      · simpa using hb
      · simpa using hcd
    exact hid ▸ h

end QuaternaryTernaryCyclicSubmodules
end SymmetricSubgroupAsymptotics

end
