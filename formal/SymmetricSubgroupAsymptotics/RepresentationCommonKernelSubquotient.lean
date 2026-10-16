import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Two actual equivariant maps with nested kernels give a literal
subquotient realization of the target in the common-coordinate module. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G E M A : Type} [Field k] [Group G]
    [AddCommGroup E] [Module k E]
    [AddCommGroup M] [Module k M]
    [AddCommGroup A] [Module k A]

def intertwinerKernelQuotient (rho : Representation k G E)
    (sigma : Representation k G M) (m : rho.IntertwiningMap sigma) :
    Representation k G (E ⧸ m.ker.toSubmodule) :=
  rho.quotient m.ker.toSubmodule (fun g => m.ker.apply_mem_toSubmodule g)

def intertwinerKernelQuotientMap (rho : Representation k G E)
    (sigma : Representation k G M) (m : rho.IntertwiningMap sigma)
    (tau : Representation k G A) (f : rho.IntertwiningMap tau)
    (hker : m.ker ≤ f.ker) :
    (intertwinerKernelQuotient rho sigma m).IntertwiningMap tau where
  toLinearMap := m.ker.toSubmodule.liftQ f.toLinearMap hker
  isIntertwining' g := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := m.ker.toSubmodule.mkQ_surjective y
    exact Representation.IntertwiningMap.isIntertwining _ _ f g x

theorem intertwinerKernelQuotientMap_surjective
    (rho : Representation k G E) (sigma : Representation k G M)
    (m : rho.IntertwiningMap sigma) (tau : Representation k G A)
    (f : rho.IntertwiningMap tau) (hker : m.ker ≤ f.ker)
    (hf : Function.Surjective f) :
    Function.Surjective (intertwinerKernelQuotientMap rho sigma m tau f hker) := by
  intro a
  obtain ⟨e, he⟩ := hf a
  exact ⟨m.ker.toSubmodule.mkQ e, he⟩

def intertwinerKernelQuotientEmbedding
    (rho : Representation k G E) (sigma : Representation k G M)
    (m : rho.IntertwiningMap sigma) :
    (intertwinerKernelQuotient rho sigma m).IntertwiningMap sigma :=
  intertwinerKernelQuotientMap rho sigma m sigma m le_rfl

theorem intertwinerKernelQuotientEmbedding_injective
    (rho : Representation k G E) (sigma : Representation k G M)
    (m : rho.IntertwiningMap sigma) :
    Function.Injective (intertwinerKernelQuotientEmbedding rho sigma m) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := m.ker.toSubmodule.mkQ_surjective x
  obtain ⟨b, rfl⟩ := m.ker.toSubmodule.mkQ_surjective y
  apply (Submodule.Quotient.eq m.ker.toSubmodule).mpr
  change m (a - b) = 0
  rw [map_sub, sub_eq_zero]
  exact hxy

end SymmetricSubgroupAsymptotics

end
