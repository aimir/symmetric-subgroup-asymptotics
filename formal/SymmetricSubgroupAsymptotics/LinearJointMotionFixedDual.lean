import SymmetricSubgroupAsymptotics.FiniteLinearJointMotionDuality

/-! The annihilator of the two actual motion images consists exactly of
the functionals fixed by both original operators. This keeps the pair
correlated: no separate fixed-space maximum or orbit census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearJointMotionFixedDual

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def jointMotion (A B : V →ₗ[K] V) : (V × V) →ₗ[K] V :=
  (A - LinearMap.id).coprod (-(B - LinearMap.id))

theorem mem_dual_kernel_iff (A B : V →ₗ[K] V) (ℓ : Module.Dual K V) :
    ℓ ∈ (jointMotion A B).dualMap.ker ↔
      (∀ v : V, ℓ (A v) = ℓ v) ∧ (∀ v : V, ℓ (B v) = ℓ v) := by
  constructor
  · intro hℓ
    have hzero : (jointMotion A B).dualMap ℓ = 0 := hℓ
    have hp (p : V × V) : ℓ (jointMotion A B p) = 0 :=
      DFunLike.congr_fun hzero p
    constructor
    · intro v
      apply sub_eq_zero.mp
      simpa only [jointMotion, LinearMap.coprod_apply, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.neg_apply, map_zero, sub_zero,
        neg_zero, add_zero, map_sub] using hp (v, 0)
    · intro v
      apply sub_eq_zero.mp
      apply neg_eq_zero.mp
      simpa only [jointMotion, LinearMap.coprod_apply, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.neg_apply, map_zero, sub_zero,
        zero_add, map_neg, map_sub] using hp (0, v)
  · rintro ⟨hA, hB⟩
    change (jointMotion A B).dualMap ℓ = 0
    apply LinearMap.ext
    intro p
    change ℓ ((A p.1 - p.1) + -(B p.2 - p.2)) = 0
    simp only [map_add, map_neg, map_sub, hA, hB, sub_self, neg_zero, add_zero]

theorem card_joint_motion_kernel [FiniteDimensional K V] (A B : V →ₗ[K] V) :
    Nat.card (jointMotion A B).ker = Nat.card V *
      Nat.card {ℓ : Module.Dual K V //
        (∀ v : V, ℓ (A v) = ℓ v) ∧ (∀ v : V, ℓ (B v) = ℓ v)} := by
  let e : (jointMotion A B).dualMap.ker ≃
      {ℓ : Module.Dual K V //
        (∀ v : V, ℓ (A v) = ℓ v) ∧ (∀ v : V, ℓ (B v) = ℓ v)} := {
    toFun := fun ℓ => ⟨ℓ.val, (mem_dual_kernel_iff A B ℓ.val).mp ℓ.property⟩
    invFun := fun ℓ => ⟨ℓ.val, (mem_dual_kernel_iff A B ℓ.val).mpr ℓ.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (FiniteLinearJointMotionDuality.card_kernel_eq_mul_dual_kernel
    (jointMotion A B)).trans (congrArg (Nat.card V * ·) (Nat.card_congr e))

end SymmetricSubgroupAsymptotics.LinearJointMotionFixedDual
