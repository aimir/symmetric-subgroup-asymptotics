import Mathlib.LinearAlgebra.Projectivization.Subspace

/-! Projective span is exactly projectivization of the linear span of
the literal chosen representatives. No coordinates or collineation
classification is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveSpanRepresentatives
variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem projectivization_span_representatives (p : I → Projectivization F V) :
    (Submodule.span F (Set.range (fun i => (p i).rep))).projectivization =
      Projectivization.Subspace.span (Set.range p) := by
  apply le_antisymm
  · have hs : Submodule.span F (Set.range (fun i => (p i).rep)) ≤
        Projectivization.Subspace.submodule
          (Projectivization.Subspace.span (Set.range p)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply (Projectivization.Subspace.mem_submodule_iff _ (p i).rep_nonzero).mpr
      simpa only [Projectivization.mk_rep] using
        (Projectivization.Subspace.subset_span (Set.range p) ⟨i, rfl⟩)
    have hh := (Submodule.projectivization (K := F) (V := V)).monotone hs
    simpa only [Submodule.projectivization, OrderIso.symm_apply_apply] using hh
  · apply Projectivization.Subspace.span_le_subspace_iff.mpr
    rintro _ ⟨i, rfl⟩
    rw [← Projectivization.mk_rep (p i)]
    exact (Submodule.mk_mem_projectivization_iff _ (p i).rep_nonzero).mpr
      (Submodule.subset_span ⟨i, rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGProjectiveSpanRepresentatives
