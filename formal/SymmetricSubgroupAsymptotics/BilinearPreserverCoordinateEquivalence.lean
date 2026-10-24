import SymmetricSubgroupAsymptotics.QuadraticIsometryPolarStabilizer

/-! Actual linear coordinates preserving a bilinear pairing conjugate
the full preserver groups. This is a coordinate transport theorem, with
the preserved pairing equality proved by each application; no form
recognition or class-count premise is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BilinearPreserverCoordinateEquivalence
open QuadraticIsometryPolarStabilizer
variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def preserverEquiv (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (E : V ≃ₗ[K] W) (hE : ∀ x y, C (E x) (E y) = B x y) :
    polarPreservers B ≃* polarPreservers C where
  toFun g := ⟨E.symm.trans (g.val.trans E), by
    intro x y
    change C (E (g.val (E.symm x))) (E (g.val (E.symm y))) = C x y
    calc
      _ = B (g.val (E.symm x)) (g.val (E.symm y)) := hE _ _
      _ = B (E.symm x) (E.symm y) := g.property _ _
      _ = C x y := by simpa only [E.apply_symm_apply] using (hE (E.symm x) (E.symm y)).symm⟩
  invFun g := ⟨E.trans (g.val.trans E.symm), by
    intro x y
    change B (E.symm (g.val (E x))) (E.symm (g.val (E y))) = B x y
    calc
      _ = C (g.val (E x)) (g.val (E y)) := by
        simpa only [E.apply_symm_apply] using
          (hE (E.symm (g.val (E x))) (E.symm (g.val (E y)))).symm
      _ = C (E x) (E y) := g.property _ _
      _ = B x y := hE _ _⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, E.apply_symm_apply, E.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, E.apply_symm_apply, E.symm_apply_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change E (g.val (h.val (E.symm x))) =
      E (g.val (E.symm (E (h.val (E.symm x)))))
    rw [E.symm_apply_apply]

theorem preserverEquiv_apply (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (E : V ≃ₗ[K] W) (hE : ∀ x y, C (E x) (E y) = B x y)
    (g : polarPreservers B) (w : W) :
    (preserverEquiv B C E hE g).val w = E (g.val (E.symm w)) := rfl

end SymmetricSubgroupAsymptotics.BilinearPreserverCoordinateEquivalence
