import SymmetricSubgroupAsymptotics.CFSGProjectiveCollineationSubspaces

/-! Exact transport of spans, and fixed coordinate spans, under the original
projective collineation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F]

private theorem inverse_mem_map (f : collineationGroup (F:=F) (n:=n))
    (S : Projectivization.Subspace F (n→F)) (p : Points (F:=F) (n:=n)) :
    p∈mapSubspace f⁻¹ S↔f.val p∈S := by
  rw [mem_mapSubspace]
  rfl

theorem mapSubspace_le_iff (f : collineationGroup (F:=F) (n:=n))
    (S T : Projectivization.Subspace F (n→F)) :
    mapSubspace f S≤T↔S≤mapSubspace f⁻¹ T := by
  constructor
  · intro h p hp
    exact (inverse_mem_map f T p).mpr (h ⟨p,hp,rfl⟩)
  · intro h p hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact (inverse_mem_map f T q).mp (h hq)

theorem mapSubspace_span (f : collineationGroup (F:=F) (n:=n))
    (S : Set (Points (F:=F) (n:=n))) :
    mapSubspace f (Projectivization.Subspace.span S)=
      Projectivization.Subspace.span ((f : Equiv.Perm (Points (F:=F) (n:=n))) '' S) := by
  apply le_antisymm
  · apply (mapSubspace_le_iff f _ _).mpr
    apply Projectivization.Subspace.span_le_subspace_iff.mpr
    intro p hp
    apply (inverse_mem_map f _ p).mpr
    exact Projectivization.Subspace.subset_span _ ⟨p,hp,rfl⟩
  · apply Projectivization.Subspace.span_le_subspace_iff.mpr
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨p,Projectivization.Subspace.subset_span S hp,rfl⟩

theorem mapSubspace_span_eq_of_fixed (f : collineationGroup (F:=F) (n:=n))
    (S : Set (Points (F:=F) (n:=n))) (hS : ∀p∈S,f.val p=p) :
    mapSubspace f (Projectivization.Subspace.span S)=Projectivization.Subspace.span S := by
  rw [mapSubspace_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    rwa [hS q hq]
  · intro hp
    exact ⟨p,hp,hS p hp⟩

theorem mem_span_fixed_iff (f : collineationGroup (F:=F) (n:=n))
    (S : Set (Points (F:=F) (n:=n))) (hS : ∀p∈S,f.val p=p)
    (p : Points (F:=F) (n:=n)) :
    f.val p∈Projectivization.Subspace.span S↔p∈Projectivization.Subspace.span S := by
  have he := mem_mapSubspace f (Projectivization.Subspace.span S) (f.val p)
  simpa only [mapSubspace_span_eq_of_fixed f S hS,Equiv.symm_apply_apply] using he

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
