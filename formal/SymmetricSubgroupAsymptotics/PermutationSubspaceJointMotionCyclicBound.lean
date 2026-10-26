import SymmetricSubgroupAsymptotics.LinearJointMotionFixedDual
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! The SAME pair of motion operators is bounded by either selected
element's actual fixed space. Rank-nullity for that single operator and
the literal subspace inclusion work in modular characteristic. This is
not monotonicity of joint coinvariants under arbitrary inclusions. The
permutation endpoint keeps its original invariant subspace and action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationSubspaceJointMotionCyclicBound
open LinearJointMotionFixedDual
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

/-- Jointly invariant forms annihilate the selected single motion.
Single-operator rank-nullity identifies its dual kernel dimension with
its ordinary fixed-space dimension. -/
theorem dual_kernel_finrank_le_left_fixed [FiniteDimensional K W]
    (A B : W →ₗ[K] W) : Module.finrank K (jointMotion A B).dualMap.ker≤
      Module.finrank K (A-LinearMap.id).ker := by
  let F : (jointMotion A B).dualMap.ker →ₗ[K] (A-LinearMap.id).dualMap.ker :=
    LinearMap.id.restrict (fun ell hell => by
      have h := ((mem_dual_kernel_iff A B ell).mp hell).1
      change (A-LinearMap.id).dualMap ell=0
      apply LinearMap.ext
      intro w
      change ell (A w-w)=0
      rw [map_sub,h,sub_self])
  have hF : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : (A-LinearMap.id).dualMap.ker => z.val) h
  have hdim : Module.finrank K (A-LinearMap.id).dualMap.ker=
      Module.finrank K (A-LinearMap.id).ker := by
    have hA := (A-LinearMap.id).finrank_range_add_finrank_ker
    have hd := (A-LinearMap.id).dualMap.finrank_range_add_finrank_ker
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range,Subspace.dual_finrank_eq] at hd
    omega
  exact (LinearMap.finrank_le_finrank_of_injective hF).trans_eq hdim

/-- Only the selected operator needs the displayed intertwining for
this bound; the other original operator remains in the joint kernel. -/
theorem dual_kernel_finrank_le_ambient_left_fixed
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : W →ₗ[K] V) (hf : Function.Injective f)
    (A B : W →ₗ[K] W) (C : V →ₗ[K] V)
    (hC : ∀ w, f (A w)=C (f w)) :
    Module.finrank K (jointMotion A B).dualMap.ker≤
      Module.finrank K (C-LinearMap.id).ker := by
  let F : (A-LinearMap.id).ker →ₗ[K] (C-LinearMap.id).ker :=
    f.restrict (fun w hw => by
      have hw' : A w=w := sub_eq_zero.mp hw
      change C (f w)-f w=0
      rw [←hC,hw',sub_self])
  have hF : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    apply hf
    exact congrArg (fun z : (C-LinearMap.id).ker => z.val) h
  exact (dual_kernel_finrank_le_left_fixed A B).trans
    (LinearMap.finrank_le_finrank_of_injective hF)

private theorem joint_dual_finrank_swap [FiniteDimensional K W]
    (A B : W →ₗ[K] W) :
    Module.finrank K (jointMotion A B).dualMap.ker=
      Module.finrank K (jointMotion B A).dualMap.ker := by
  have he : (jointMotion A B).dualMap.ker=(jointMotion B A).dualMap.ker := by
    ext ell
    rw [mem_dual_kernel_iff,mem_dual_kernel_iff]
    exact and_comm
  exact congrArg (fun N : Submodule K (Module.Dual K W) => Module.finrank K N) he

/-- Both fixed-space bounds concern the same original pair and the
same embedding, before taking their minimum. -/
theorem dual_kernel_finrank_le_ambient_fixed_min
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : W →ₗ[K] V) (hf : Function.Injective f)
    (A B : W →ₗ[K] W) (C D : V →ₗ[K] V)
    (hC : ∀ w, f (A w)=C (f w)) (hD : ∀ w, f (B w)=D (f w)) :
    Module.finrank K (jointMotion A B).dualMap.ker≤
      min (Module.finrank K (C-LinearMap.id).ker)
        (Module.finrank K (D-LinearMap.id).ker) := by
  apply le_min (dual_kernel_finrank_le_ambient_left_fixed f hf A B C hC)
  exact (joint_dual_finrank_swap A B).le.trans
    (dual_kernel_finrank_le_ambient_left_fixed f hf B A D hD)

/-- The literal unsigned permutation subrepresentation keeps both
actual group elements. Its joint coindimension is bounded by the number
of original cyclic orbits of the first selected element. -/
theorem subspace_joint_finrank_le_cyclic_orbits
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (M : Subrepresentation (permutationFunctionRepresentation K G X)) (g h : G) :
    Module.finrank K
      (jointMotion (M.toRepresentation g) (M.toRepresentation h)).dualMap.ker≤
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) := by
  letI : Fintype X := Fintype.ofFinite X
  have hb := dual_kernel_finrank_le_ambient_left_fixed M.toSubmodule.subtype
    M.toSubmodule.injective_subtype (M.toRepresentation g) (M.toRepresentation h)
    (permutationFunctionRepresentation K G X g) (fun _ => rfl)
  exact hb.trans (permutation_elementFixedSpace_le_cyclicOrbitCount (k:=K) g)

/-- The unsigned permutation specialization retains the actual pair
and takes the minimum only after both actual cyclic-orbit bounds. -/
theorem subspace_joint_finrank_le_min_cyclic_orbits
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (M : Subrepresentation (permutationFunctionRepresentation K G X)) (g h : G) :
    Module.finrank K
      (jointMotion (M.toRepresentation g) (M.toRepresentation h)).dualMap.ker≤
      min (Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X))
        (Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers h) X)) := by
  letI : Fintype X := Fintype.ofFinite X
  apply le_min (subspace_joint_finrank_le_cyclic_orbits M g h)
  exact (joint_dual_finrank_swap (M.toRepresentation g) (M.toRepresentation h)).le.trans
    (subspace_joint_finrank_le_cyclic_orbits M h g)

end SymmetricSubgroupAsymptotics.PermutationSubspaceJointMotionCyclicBound
