import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! A nondegenerate reference form identifies actual bilinear forms
with endomorphisms. Preserved forms become commuting operators and
pullback becomes adjoint congruence. This does not classify any orbit
of forms, and does not identify characteristic-two quadratic forms
having the same polar form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.InvariantBilinearFormCentralizer

open LinearMap
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

def operatorEquiv (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) :
    LinearMap.BilinForm K V ≃ₗ[K] Module.End K V :=
  LinearEquiv.congrRight (B.toDual hB).symm

theorem operatorEquiv_apply (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (C : LinearMap.BilinForm K V) (x y : V) :
    B (operatorEquiv B hB C x) y = C x y := by
  change B ((B.toDual hB).symm (C x)) y = C x y
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (C x) y

theorem nondegenerate_iff_bijective (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (C : LinearMap.BilinForm K V) :
    C.Nondegenerate ↔ Function.Bijective (operatorEquiv B hB C) := by
  constructor
  · intro hC
    constructor
    · intro x y he
      apply (C.toDual hC).injective
      apply (B.toDual hB).symm.injective
      exact he
    · intro z
      obtain ⟨x, hx⟩ := (C.toDual hC).surjective ((B.toDual hB) z)
      refine ⟨x, ?_⟩
      change (B.toDual hB).symm (C x) = z
      change C x = (B.toDual hB) z at hx
      rw [hx, LinearEquiv.symm_apply_apply]
  · intro hC
    refine ⟨?_, ?_⟩
    · intro x hx
      have hz : operatorEquiv B hB C x = 0 := hB.1 _ (fun y =>
        (operatorEquiv_apply B hB C x y).trans (hx y))
      apply hC.1
      simpa only [map_zero] using hz
    · intro y hy
      apply hB.2 y
      intro x
      obtain ⟨z, rfl⟩ := hC.2 x
      exact (operatorEquiv_apply B hB C z y).trans (hy z)

theorem alternating_iff (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (C : LinearMap.BilinForm K V) :
    C.IsAlt ↔ ∀ x : V, B (operatorEquiv B hB C x) x = 0 := by
  constructor
  · intro hC x
    exact (operatorEquiv_apply B hB C x x).trans (hC x)
  · intro hC x
    exact (operatorEquiv_apply B hB C x x).symm.trans (hC x)

theorem invariant_iff_commute (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (A : V ≃ₗ[K] V) (hA : ∀ x y : V, B (A x) (A y) = B x y)
    (C : LinearMap.BilinForm K V) :
    (∀ x y : V, C (A x) (A y) = C x y) ↔
      Commute (operatorEquiv B hB C) A.toLinearMap := by
  constructor
  · intro hC
    apply LinearMap.ext
    intro x
    change operatorEquiv B hB C (A x) = A (operatorEquiv B hB C x)
    apply (B.toDual hB).injective
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := A.surjective y
    change B (operatorEquiv B hB C (A x)) (A z) =
      B (A (operatorEquiv B hB C x)) (A z)
    calc
      _ = C (A x) (A z) := operatorEquiv_apply B hB C (A x) (A z)
      _ = C x z := hC x z
      _ = B (operatorEquiv B hB C x) z := (operatorEquiv_apply B hB C x z).symm
      _ = _ := (hA (operatorEquiv B hB C x) z).symm
  · intro hC x y
    have hx : operatorEquiv B hB C (A x) = A (operatorEquiv B hB C x) :=
      LinearMap.congr_fun hC x
    calc
      C (A x) (A y) = B (operatorEquiv B hB C (A x)) (A y) :=
        (operatorEquiv_apply B hB C (A x) (A y)).symm
      _ = B (A (operatorEquiv B hB C x)) (A y) := congrArg (fun z : V => B z (A y)) hx
      _ = B (operatorEquiv B hB C x) y := hA (operatorEquiv B hB C x) y
      _ = C x y := operatorEquiv_apply B hB C x y

theorem operatorEquiv_pullback (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (C : LinearMap.BilinForm K V) (T : Module.End K V) :
    operatorEquiv B hB (C.comp T T) =
      (B.leftAdjointOfNondegenerate hB T).comp ((operatorEquiv B hB C).comp T) := by
  apply LinearMap.ext
  intro x
  apply (B.toDual hB).injective
  apply LinearMap.ext
  intro y
  change B (operatorEquiv B hB (C.comp T T) x) y =
    B (B.leftAdjointOfNondegenerate hB T (operatorEquiv B hB C (T x))) y
  calc
    _ = (C.comp T T) x y := operatorEquiv_apply B hB (C.comp T T) x y
    _ = C (T x) (T y) := rfl
    _ = B (operatorEquiv B hB C (T x)) (T y) :=
      (operatorEquiv_apply B hB C (T x) (T y)).symm
    _ = _ := (B.isAdjointPairLeftAdjointOfNondegenerate hB T
      (operatorEquiv B hB C (T x)) y).symm

end SymmetricSubgroupAsymptotics.InvariantBilinearFormCentralizer
