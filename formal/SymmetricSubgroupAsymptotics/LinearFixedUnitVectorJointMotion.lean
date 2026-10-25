import SymmetricSubgroupAsymptotics.LinearJointMotionSubspaceMinBound

/-! A fixed vector of augmentation one gives a genuine equivariant
surjection onto the actual augmentation kernel. Pullback along this
surjection injects the jointly fixed duals. Both operators and the same
kernel are retained, in arbitrary characteristic; no submodule
coinvariant-monotonicity or semisimplicity assertion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LinearFixedUnitVectorJointMotion
open LinearJointMotionFixedDual
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

/-- Coinvariant dimension is monotone under an ACTUAL equivariant
surjection, via the injective dual pullback. -/
theorem dual_kernel_finrank_le_of_surjective
    [FiniteDimensional K V] [FiniteDimensional K W]
    (p : V →ₗ[K] W) (hp : Function.Surjective p)
    (A B : W →ₗ[K] W) (C D : V →ₗ[K] V)
    (hC : ∀ v, p (C v)=A (p v)) (hD : ∀ v, p (D v)=B (p v)) :
    Module.finrank K (jointMotion A B).dualMap.ker≤
      Module.finrank K (jointMotion C D).dualMap.ker := by
  let F : (jointMotion A B).dualMap.ker →ₗ[K] (jointMotion C D).dualMap.ker :=
    p.dualMap.restrict (fun ell hell => by
      have h := (mem_dual_kernel_iff A B ell).mp hell
      apply (mem_dual_kernel_iff C D (p.dualMap ell)).mpr
      constructor
      · intro v
        change ell (p (C v))=ell (p v)
        rw [hC]
        exact h.1 (p v)
      · intro v
        change ell (p (D v))=ell (p v)
        rw [hD]
        exact h.2 (p v))
  have hF : Function.Injective F := by
    intro ell m h
    apply Subtype.ext
    apply LinearMap.dualMap_injective_of_surjective hp
    exact congrArg (fun z : (jointMotion C D).dualMap.ker => z.val) h
  exact LinearMap.finrank_le_finrank_of_injective hF

/-- The literal projection along the selected vector of functional one. -/
def kernelRetraction (epsilon : V →ₗ[K] K) (u : V) (hu : epsilon u=1) :
    V →ₗ[K] epsilon.ker :=
  (LinearMap.id-epsilon.smulRight u).codRestrict epsilon.ker (by
    intro v
    change epsilon (v-epsilon v • u)=0
    simp only [map_sub,map_smul,hu,smul_eq_mul,mul_one,sub_self])

theorem kernelRetraction_surjective (epsilon : V →ₗ[K] K) (u : V)
    (hu : epsilon u=1) : Function.Surjective (kernelRetraction epsilon u hu) := by
  intro n
  refine ⟨n.val,?_⟩
  apply Subtype.ext
  change n.val-epsilon n.val • u=n.val
  have hn : epsilon n.val=0 := n.property
  rw [hn,zero_smul,sub_zero]

/-- An operator preserving the displayed functional induces its actual
restriction to the literal kernel. -/
def kernelEnd (epsilon : V →ₗ[K] K) (C : V →ₗ[K] V)
    (hC : ∀ v, epsilon (C v)=epsilon v) : epsilon.ker →ₗ[K] epsilon.ker :=
  C.restrict (fun v hv => by
    change epsilon (C v)=0
    rw [hC]
    exact hv)

theorem kernelRetraction_intertwines (epsilon : V →ₗ[K] K) (u : V)
    (hu : epsilon u=1) (C : V →ₗ[K] V)
    (hC : ∀ v, epsilon (C v)=epsilon v) (hCu : C u=u) (v : V) :
    kernelRetraction epsilon u hu (C v)=
      kernelEnd epsilon C hC (kernelRetraction epsilon u hu v) := by
  apply Subtype.ext
  change C v-epsilon (C v) • u=C (v-epsilon v • u)
  rw [hC,map_sub,map_smul,hCu]

/-- A common invariant vector of functional one pays the joint-motion
coindimension of the SAME kernel by the ambient joint coindimension. -/
theorem dual_kernel_finrank_le_of_fixed_unit_vector [FiniteDimensional K V]
    (epsilon : V →ₗ[K] K) (u : V) (hu : epsilon u=1)
    (C D : V →ₗ[K] V)
    (hC : ∀ v, epsilon (C v)=epsilon v) (hD : ∀ v, epsilon (D v)=epsilon v)
    (hCu : C u=u) (hDu : D u=u) :
    Module.finrank K (jointMotion (kernelEnd epsilon C hC) (kernelEnd epsilon D hD)).dualMap.ker≤
      Module.finrank K (jointMotion C D).dualMap.ker := by
  exact dual_kernel_finrank_le_of_surjective (kernelRetraction epsilon u hu)
    (kernelRetraction_surjective epsilon u hu)
    (kernelEnd epsilon C hC) (kernelEnd epsilon D hD) C D
    (kernelRetraction_intertwines epsilon u hu C hC hCu)
    (kernelRetraction_intertwines epsilon u hu D hD hDu)

end SymmetricSubgroupAsymptotics.LinearFixedUnitVectorJointMotion
