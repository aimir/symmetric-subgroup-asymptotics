import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! A literal nondegenerate two-plane has a literal common-kernel
complement. Its pointwise isometry fixer acts faithfully on that
complement, even when the full ambient form is degenerate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BilinearPairFixerRestriction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (B : LinearMap.BilinForm K V) (u w : V)

def complement : Submodule K V := (B u).ker ⊓ (B w).ker

def residual (v : V) : V := v - B w v • u - B u v • w

theorem residual_mem (hu : B u u = 0) (hw : B w w = 0)
    (huw : B u w = 1) (hwu : B w u = 1) (v : V) :
    residual B u w v ∈ complement B u w := by
  constructor
  · change B u (v - B w v • u - B u v • w) = 0
    rw [map_sub, map_sub, map_smul, map_smul, hu, huw]
    simp only [smul_eq_mul, mul_zero, mul_one, sub_zero, sub_self]
  · change B w (v - B w v • u - B u v • w) = 0
    rw [map_sub, map_sub, map_smul, map_smul, hw, hwu]
    simp only [smul_eq_mul, mul_zero, mul_one, sub_self]

theorem residual_decomposition (v : V) :
    residual B u w v + B w v • u + B u v • w = v := by
  dsimp only [residual]
  abel

/-- Both codimensions are computed from actual nonzero functionals. -/
theorem complement_finrank [Module.Finite K V]
    (hu : B u u = 0) (huw : B u w = 1) (hwu : B w u = 1) :
    Module.finrank K (complement B u w) = Module.finrank K V - 2 := by
  let W := (B u).ker
  let g : Module.Dual K W := (B w).comp W.subtype
  let uW : W := ⟨u, hu⟩
  have hBu : B u ≠ 0 := by
    intro he
    have hz : B u w = 0 := by rw [he, LinearMap.zero_apply]
    exact zero_ne_one (hz.symm.trans huw)
  have hg : g ≠ 0 := by
    intro he
    have hz : g uW = 0 := by rw [he, LinearMap.zero_apply]
    have hgu : g uW = 1 := hwu
    exact zero_ne_one (hz.symm.trans hgu)
  let e : complement B u w ≃ₗ[K] g.ker := {
    toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hd₁ : Module.finrank K W + 1 = Module.finrank K V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hBu
  have hd₂ : Module.finrank K g.ker + 1 = Module.finrank K W :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hg
  have he := e.finrank_eq
  omega

/-- The actual simultaneous pointwise fixer, with its actual preserved form. -/
abbrev Fixer := {e : V ≃ₗ[K] V //
  (∀ x y : V, B (e x) (e y) = B x y) ∧ e u = u ∧ e w = w}

private theorem apply_mem (e : Fixer B u w) (x : complement B u w) :
    e.val x.val ∈ complement B u w := by
  constructor
  · change B u (e.val x.val) = 0
    calc
      _ = B (e.val u) (e.val x.val) := congrArg (fun z => B z (e.val x.val)) e.property.2.1.symm
      _ = B u x.val := e.property.1 u x.val
      _ = 0 := x.property.1
  · change B w (e.val x.val) = 0
    calc
      _ = B (e.val w) (e.val x.val) := congrArg (fun z => B z (e.val x.val)) e.property.2.2.symm
      _ = B w x.val := e.property.1 w x.val
      _ = 0 := x.property.2

private def inverseFixer (e : Fixer B u w) : Fixer B u w :=
  ⟨e.val.symm, by
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      have he := e.property.1 (e.val.symm x) (e.val.symm y)
      simpa only [LinearEquiv.apply_symm_apply] using he.symm
    · apply e.val.injective
      rw [LinearEquiv.apply_symm_apply, e.property.2.1]
    · apply e.val.injective
      rw [LinearEquiv.apply_symm_apply, e.property.2.2]⟩

/-- Restriction is an actual linear equivalence on the actual complement. -/
def restriction (e : Fixer B u w) :
    complement B u w ≃ₗ[K] complement B u w where
  toFun x := ⟨e.val x.val, apply_mem B u w e x⟩
  invFun x := ⟨e.val.symm x.val, apply_mem B u w (inverseFixer B u w e) x⟩
  left_inv x := by apply Subtype.ext; exact e.val.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.val.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact e.val.map_add x.val y.val
  map_smul' a x := by apply Subtype.ext; exact e.val.map_smul a x.val

/-- The full ambient map is recovered from its restriction and the two fixed vectors. -/
theorem restriction_injective (hu : B u u = 0) (hw : B w w = 0)
    (huw : B u w = 1) (hwu : B w u = 1) :
    Function.Injective (restriction B u w) := by
  intro e f he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  let r : complement B u w := ⟨residual B u w v, residual_mem B u w hu hw huw hwu v⟩
  have hr : e.val r.val = f.val r.val :=
    congrArg (fun g : complement B u w ≃ₗ[K] complement B u w => (g r).val) he
  calc
    e.val v = e.val (r.val + B w v • u + B u v • w) :=
      congrArg e.val (residual_decomposition B u w v).symm
    _ = e.val r.val + B w v • u + B u v • w := by
      rw [map_add, map_add, map_smul, map_smul, e.property.2.1, e.property.2.2]
    _ = f.val r.val + B w v • u + B u v • w := congrArg (fun z => z + B w v • u + B u v • w) hr
    _ = f.val (r.val + B w v • u + B u v • w) := by
      rw [map_add, map_add, map_smul, map_smul, f.property.2.1, f.property.2.2]
    _ = f.val v := congrArg f.val (residual_decomposition B u w v)

theorem fixer_card_le [Finite V]
    (hu : B u u = 0) (hw : B w w = 0)
    (huw : B u w = 1) (hwu : B w u = 1) :
    Nat.card (Fixer B u w) ≤
      Nat.card (complement B u w ≃ₗ[K] complement B u w) := by
  let R := complement B u w
  letI : Finite (R ≃ₗ[K] R) := Finite.of_injective
    (fun e : R ≃ₗ[K] R => (e : R → R)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective (restriction B u w)
    (restriction_injective B u w hu hw huw hwu)

end SymmetricSubgroupAsymptotics.BilinearPairFixerRestriction
