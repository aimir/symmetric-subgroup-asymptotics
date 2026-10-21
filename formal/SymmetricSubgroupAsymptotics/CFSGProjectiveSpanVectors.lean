import SymmetricSubgroupAsymptotics.CFSGProjectiveSpanRepresentatives

/-! The projective span of literal nonzero vectors is exactly the
projectivization of their original linear span. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics
variable {F V I : Type*} [DivisionRing F] [AddCommGroup V] [Module F V]

theorem projectivization_span_vectors (v : I→V) (hv : ∀i,v i≠0) :
    (Submodule.span F (Set.range v)).projectivization=
      Projectivization.Subspace.span (Set.range (fun i => Projectivization.mk F (v i) (hv i))) := by
  let L := Submodule.span F (Set.range v)
  let S := Projectivization.Subspace.span
    (Set.range (fun i => Projectivization.mk F (v i) (hv i)))
  apply le_antisymm
  · have hL : L≤Projectivization.Subspace.submodule S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      apply (Projectivization.Subspace.mem_submodule_iff S (hv i)).mpr
      exact Projectivization.Subspace.subset_span _ ⟨i,rfl⟩
    simpa only [Submodule.projectivization,OrderIso.symm_apply_apply] using
      Submodule.projectivization.monotone hL
  · apply Projectivization.Subspace.span_le_subspace_iff.mpr
    rintro _ ⟨i,rfl⟩
    exact (Submodule.mk_mem_projectivization_iff L (hv i)).mpr
      (Submodule.subset_span ⟨i,rfl⟩)

end SymmetricSubgroupAsymptotics
