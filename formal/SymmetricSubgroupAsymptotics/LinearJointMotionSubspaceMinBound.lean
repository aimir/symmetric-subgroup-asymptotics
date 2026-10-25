import SymmetricSubgroupAsymptotics.LinearJointMotionFixedDual
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Joint-motion coindimension in an ACTUAL invariant subspace. The two
operators and the one embedding are retained. Kernel injection and
rank-nullity give min(dimW, ambient coindimension+codimW), also in modular
characteristic; no false submodule-coinvariant monotonicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearJointMotionSubspaceMinBound
open LinearJointMotionFixedDual
variable {K W V : Type*} [Field K] [AddCommGroup W] [Module K W]
    [AddCommGroup V] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K W] [FiniteDimensional K V] in
private theorem joint_intertwine (f : W →ₗ[K] V)
    (A B : W →ₗ[K] W) (C D : V →ₗ[K] V)
    (hA : ∀ w, f (A w)=C (f w)) (hB : ∀ w, f (B w)=D (f w)) (w : W×W) :
    jointMotion C D (f w.1,f w.2)=f (jointMotion A B w) := by
  simp only [jointMotion,LinearMap.coprod_apply,LinearMap.sub_apply,LinearMap.id_apply,
    LinearMap.neg_apply,map_add,map_neg,map_sub,hA,hB]

theorem dual_kernel_finrank_le_min (f : W →ₗ[K] V) (hf : Function.Injective f)
    (A B : W →ₗ[K] W) (C D : V →ₗ[K] V)
    (hA : ∀ w, f (A w)=C (f w)) (hB : ∀ w, f (B w)=D (f w)) :
    Module.finrank K (jointMotion A B).dualMap.ker≤
      min (Module.finrank K W)
        (Module.finrank K (jointMotion C D).dualMap.ker+
          (Module.finrank K V-Module.finrank K W)) := by
  let F : (jointMotion A B).ker →ₗ[K] (jointMotion C D).ker :=
    { toFun := fun w => ⟨(f w.val.1,f w.val.2),by
        change jointMotion C D (f w.val.1,f w.val.2)=0
        rw [joint_intertwine f A B C D hA hB w.val,w.property,map_zero]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact Prod.ext (f.map_add x.val.1 y.val.1) (f.map_add x.val.2 y.val.2)
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact Prod.ext (f.map_smul c x.val.1) (f.map_smul c x.val.2) }
  have hF : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext (hf (congrArg (fun w : (jointMotion C D).ker => w.val.1) h))
      (hf (congrArg (fun w : (jointMotion C D).ker => w.val.2) h))
  have hker := LinearMap.finrank_le_finrank_of_injective hF
  have hW := FiniteLinearJointMotionDuality.finrank_kernel_eq_add_dual_kernel (jointMotion A B)
  have hV := FiniteLinearJointMotionDuality.finrank_kernel_eq_add_dual_kernel (jointMotion C D)
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  have hleft : Module.finrank K (jointMotion A B).dualMap.ker≤Module.finrank K W := by
    simpa only [Subspace.dual_finrank_eq] using Submodule.finrank_le (jointMotion A B).dualMap.ker
  apply le_min hleft
  omega

theorem card_kernel_le_min [Finite K] (f : W →ₗ[K] V) (hf : Function.Injective f)
    (A B : W →ₗ[K] W) (C D : V →ₗ[K] V)
    (hA : ∀ w, f (A w)=C (f w)) (hB : ∀ w, f (B w)=D (f w)) :
    Nat.card (jointMotion A B).ker≤Nat.card W*
      Nat.card K^min (Module.finrank K W)
        (Module.finrank K (jointMotion C D).dualMap.ker+
          (Module.finrank K V-Module.finrank K W)) := by
  rw [FiniteLinearJointMotionDuality.card_kernel_eq_mul_dual_kernel]
  rw [Module.natCard_eq_pow_finrank (K:=K) (V:=(jointMotion A B).dualMap.ker)]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.card_pos (α:=K))
    (dual_kernel_finrank_le_min f hf A B C D hA hB))

end SymmetricSubgroupAsymptotics.LinearJointMotionSubspaceMinBound
