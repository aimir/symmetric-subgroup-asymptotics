import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel

/-! The stabilizer of the actual zero vector in an affine action is exactly
its displayed linear complement. This statement does not identify an
arbitrary subgroup of the same order with the stabilizer. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.AffineModel

variable {p d : ℕ} [Fact p.Prime] (R : Subgroup (GLV p d))

/-- Stabilizer defined by the original affine action homomorphism. -/
def zeroStabilizer : Subgroup (Aff R) :=
  (MulAction.stabilizer (Equiv.Perm (V p d)) (0 : V p d)).comap (action R)

theorem mem_zeroStabilizer (g : Aff R) :
    g ∈ zeroStabilizer R ↔ g.left = 1 := by
  change action R g 0 = 0 ↔ g.left = 1
  rw [action_apply, map_zero, add_zero]
  exact Multiplicative.toAdd.injective.eq_iff

/-- Projection and the actual zero-translation section are inverse. -/
def zeroStabilizerEquiv : zeroStabilizer R ≃* R where
  toFun g := g.1.right
  invFun r := ⟨SemidirectProduct.inr r,
    (mem_zeroStabilizer R _).mpr rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact ((mem_zeroStabilizer R g.1).mp g.2).symm
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem zeroStabilizerEquiv_apply (g : zeroStabilizer R) :
    zeroStabilizerEquiv R g = g.1.right := rfl

/-- An exact affine action chart restricts to the original point stabilizer.
The equation on points is essential: an abstract group chart alone does not
identify the subgroup which fixes the chosen point. -/
def pointStabilizerEquiv
    {X : Type} (G : Subgroup (Equiv.Perm X))
    (eG : G ≃* Aff R) (eX : V p d ≃ X)
    (hact : ∀ (g : G) (v : V p d),
      eX (action R (eG g) v) = g.1 (eX v)) :
    MulAction.stabilizer G (eX 0) ≃* R :=
  (show MulAction.stabilizer G (eX 0) ≃* zeroStabilizer R from {
    toFun g := ⟨eG g.1, by
      change action R (eG g.1) 0 = 0
      apply eX.injective
      rw [hact]
      exact g.2⟩
    invFun g := ⟨eG.symm g.1, by
      change (eG.symm g.1).1 (eX 0) = eX 0
      rw [← hact, eG.apply_symm_apply]
      exact congrArg eX (show action R g.1 0 = 0 from g.2)⟩
    left_inv g := by
      apply Subtype.ext
      exact eG.symm_apply_apply g.1
    right_inv g := by
      apply Subtype.ext
      exact eG.apply_symm_apply g.1
    map_mul' g h := by
      apply Subtype.ext
      exact eG.map_mul g.1 h.1 }).trans (zeroStabilizerEquiv R)

end SymmetricSubgroupAsymptotics.AffineModel

end
