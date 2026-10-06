import Mathlib.RepresentationTheory.Intertwining

/-!
# Constructing an intertwiner from generator equations

Finite certificate rows store matrices only for a displayed generating
tuple.  The subgroup below proves once and for all that checking the
intertwining equation on those generators is enough.  This keeps generated
frame files linear in the number of generator matrices.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G V W ι : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  (rho : Representation k G V) (sigma : Representation k G W)
  (f : V →ₗ[k] W)

/-- Group elements on which a fixed linear map intertwines two
representations. -/
def representationIntertwiningSubgroup : Subgroup G where
  carrier := {g | ∀ v, f (rho g v) = sigma g (f v)}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro g h hg hh v
    calc
      f (rho (g * h) v) = f (rho g (rho h v)) := by
        rw [map_mul, Module.End.mul_apply]
      _ = sigma g (f (rho h v)) := hg _
      _ = sigma g (sigma h (f v)) := congrArg (sigma g) (hh v)
      _ = sigma (g * h) (f v) := by
        rw [map_mul, Module.End.mul_apply]
  inv_mem' := by
    intro g hg v
    have h := congrArg (fun z : W => sigma g⁻¹ z) (hg (rho g⁻¹ v))
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      inv_mul_cancel, map_one, Module.End.one_apply] at h
    exact h.symm

/-- Package a linear map as an intertwiner after checking it only on a
generating tuple. -/
def representationIntertwiningMap_of_generators
    (generators : ι → G)
    (hgenerates : Subgroup.closure (Set.range generators) = ⊤)
    (hgenerator : ∀ i v,
      f (rho (generators i) v) = sigma (generators i) (f v)) :
    rho.IntertwiningMap sigma where
  toLinearMap := f
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    have hle : Subgroup.closure (Set.range generators) ≤
        representationIntertwiningSubgroup rho sigma f :=
      (Subgroup.closure_le _).mpr (by
        rintro _ ⟨i, rfl⟩
        exact hgenerator i)
    have hg : g ∈ representationIntertwiningSubgroup rho sigma f := by
      apply hle
      rw [hgenerates]
      exact Subgroup.mem_top g
    exact hg v

end SymmetricSubgroupAsymptotics

end
