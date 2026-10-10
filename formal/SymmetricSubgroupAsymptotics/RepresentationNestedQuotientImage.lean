import SymmetricSubgroupAsymptotics.RepresentationSelfDualNestedQuotient
import SymmetricSubgroupAsymptotics.RepresentationHeadExact
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-!
# A nested quotient as the image of an intertwiner

If the kernel of a surjective representation map lies in an invariant
subrepresentation `M`, then the image of `M` is literally `M / ker(q)`.
This file packages the representation equivalence and transfers a generator
certificate for the dual nested quotient to the dual image.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

universe u

variable {k G V W : Type u} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Restrict an intertwiner to an invariant source and corestrict it to its
exact invariant image. -/
noncomputable def subrepresentationImageIntertwiner
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) (M : Subrepresentation rho) :
    M.toRepresentation.IntertwiningMap
      (intertwinerImage rho tau q M).toRepresentation where
  toLinearMap :=
    { toFun := fun x => ⟨q x.1, ⟨x.1, x.2, rfl⟩⟩
      map_add' := by intro x y; exact Subtype.ext (map_add q x.1 y.1)
      map_smul' := by intro c x; exact Subtype.ext (map_smul q c x.1) }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining rho tau q g x.1

theorem subrepresentationImageIntertwiner_surjective
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) (M : Subrepresentation rho) :
    Function.Surjective (subrepresentationImageIntertwiner rho tau q M) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Quotient `M` by the contained kernel of `q` and map it onto the exact
image of `M`. -/
noncomputable def nestedQuotientImageIntertwiner
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) (M : Subrepresentation rho)
    (hker : q.ker ≤ M) :
    (nestedQuotientRepresentation q.ker M hker).IntertwiningMap
      (intertwinerImage rho tau q M).toRepresentation where
  toLinearMap :=
    (nestedSubrepresentation q.ker M hker).toSubmodule.liftQ
      (subrepresentationImageIntertwiner rho tau q M).toLinearMap (by
        intro x hx
        apply Subtype.ext
        exact hx)
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ :=
      (nestedSubrepresentation q.ker M hker).toSubmodule.mkQ_surjective y
    exact Representation.IntertwiningMap.isIntertwining _ _
      (subrepresentationImageIntertwiner rho tau q M) g x

theorem nestedQuotientImageIntertwiner_injective
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) (M : Subrepresentation rho)
    (hker : q.ker ≤ M) :
    Function.Injective (nestedQuotientImageIntertwiner rho tau q M hker) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ :=
    (nestedSubrepresentation q.ker M hker).toSubmodule.mkQ_surjective x
  obtain ⟨b, rfl⟩ :=
    (nestedSubrepresentation q.ker M hker).toSubmodule.mkQ_surjective y
  apply Submodule.Quotient.eq.mpr
  change q (a.1 - b.1) = 0
  rw [map_sub, sub_eq_zero]
  exact congrArg Subtype.val hxy

theorem nestedQuotientImageIntertwiner_surjective
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) (M : Subrepresentation rho)
    (hker : q.ker ≤ M) :
    Function.Surjective (nestedQuotientImageIntertwiner rho tau q M hker) := by
  intro y
  obtain ⟨x, hx⟩ :=
    subrepresentationImageIntertwiner_surjective rho tau q M y
  exact ⟨Submodule.Quotient.mk x, hx⟩

/-- The exact image of `M` is representation-equivalent to `M / ker(q)`. -/
noncomputable def nestedQuotientImageEquiv
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) (M : Subrepresentation rho)
    (hker : q.ker ≤ M) :
    (nestedQuotientRepresentation q.ker M hker).Equiv
      (intertwinerImage rho tau q M).toRepresentation :=
  (nestedQuotientImageIntertwiner rho tau q M hker).ofBijective
    ⟨nestedQuotientImageIntertwiner_injective rho tau q M hker,
      nestedQuotientImageIntertwiner_surjective rho tau q M hker⟩

/-- A generator bound for the dual nested quotient transfers to the dual of
the exact image. -/
theorem image_dual_generated_of_nestedQuotient_dual_generated
    (rho : Representation k G V) (tau : Representation k G W)
    (q : rho.IntertwiningMap tau) (M : Subrepresentation rho)
    (hker : q.ker ≤ M) (H : ℕ)
    (hgen : RepresentationGeneratedBy
      (nestedQuotientRepresentation q.ker M hker).dual H) :
    RepresentationGeneratedBy
      (intertwinerImage rho tau q M).toRepresentation.dual H := by
  let E := nestedQuotientImageEquiv rho tau q M hker
  let d := RepresentationHeadExact.dualMap E.symm.toIntertwiningMap
  have hd : Function.Surjective d :=
    LinearMap.dualMap_surjective_of_injective E.symm.injective
  exact representationGeneratedBy_of_surjective _ _ d hd hgen

end SymmetricSubgroupAsymptotics

end
