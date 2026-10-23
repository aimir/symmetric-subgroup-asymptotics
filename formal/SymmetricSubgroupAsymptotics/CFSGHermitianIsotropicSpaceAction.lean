import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalClosure

/-! The point action extends to the full isotropic-subspace order once
maximal isotropic spaces separate its literal vectors. This construction
retains exact point incidence and is reversible. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

abbrev IsotropicSpace := {S : Submodule K (I → K) // Orthogonal sigma H S S}

def isotropicSpaceImage (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) (S : IsotropicSpace sigma H) : IsotropicSpace sigma H :=
  ⟨pointSpan sigma H (f '' pointSet sigma H S.val),
    (pointSpan_orthogonal_iff sigma H _).mpr
      (image_isClique sigma H f hf (pointSet_isClique sigma H S.val S.property))⟩

variable (hsep : ∀ S : IsotropicSpace sigma H, SeparatedByMaximal sigma H S.val)
include hsep

theorem isotropicSpaceImage_pointSet (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) (S : IsotropicSpace sigma H) :
    pointSet sigma H (isotropicSpaceImage sigma H f hf S).val = f '' pointSet sigma H S.val :=
  pointSet_imageSpan_eq sigma H f hf S.val (hsep S) (hsep (isotropicSpaceImage sigma H f hf S))

theorem isotropicSpaceImage_symm (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) (S : IsotropicSpace sigma H) :
    isotropicSpaceImage sigma H f.symm (preservesOrthogonality_symm sigma H f hf)
      (isotropicSpaceImage sigma H f hf S) = S := by
  apply Subtype.ext
  change pointSpan sigma H (f.symm '' pointSet sigma H (isotropicSpaceImage sigma H f hf S).val) = S.val
  rw [isotropicSpaceImage_pointSet sigma H hsep]
  have he : f.symm '' (f '' pointSet sigma H S.val) = pointSet sigma H S.val := by
    ext P
    constructor
    · rintro ⟨_, ⟨Q, hQ, rfl⟩, he⟩
      rw [f.symm_apply_apply] at he
      exact he ▸ hQ
    · intro hP
      exact ⟨f P, Set.mem_image_of_mem f hP, f.symm_apply_apply P⟩
  rw [he, pointSpan_pointSet_eq sigma H S.val S.property]

def isotropicSpaceEquiv (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) : Equiv.Perm (IsotropicSpace sigma H) where
  toFun := isotropicSpaceImage sigma H f hf
  invFun := isotropicSpaceImage sigma H f.symm (preservesOrthogonality_symm sigma H f hf)
  left_inv := isotropicSpaceImage_symm sigma H hsep f hf
  right_inv := by
    intro S
    simpa only [Equiv.symm_symm] using isotropicSpaceImage_symm sigma H hsep f.symm
      (preservesOrthogonality_symm sigma H f hf) S

theorem isotropicSpaceEquiv_incidence (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) (S : IsotropicSpace sigma H)
    (P : SingularPoint sigma H) :
    (f P).val ≤ (isotropicSpaceEquiv sigma H hsep f hf S).val ↔ P.val ≤ S.val := by
  change f P ∈ pointSet sigma H (isotropicSpaceImage sigma H f hf S).val ↔
    P ∈ pointSet sigma H S.val
  rw [isotropicSpaceImage_pointSet sigma H hsep]
  constructor
  · rintro ⟨Q, hQ, he⟩
    exact (f.injective he) ▸ hQ
  · intro hP
    exact Set.mem_image_of_mem f hP

omit hsep in
theorem pointSet_subset_iff (S T : IsotropicSpace sigma H) :
    pointSet sigma H S.val ⊆ pointSet sigma H T.val ↔ S.val ≤ T.val := by
  constructor
  · intro h
    rw [← pointSpan_pointSet_eq sigma H S.val S.property]
    exact iSup_le (fun P => h P.property)
  · exact pointSet_mono sigma H

theorem isotropicSpaceImage_le_iff (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) (S T : IsotropicSpace sigma H) :
    (isotropicSpaceImage sigma H f hf S).val ≤ (isotropicSpaceImage sigma H f hf T).val ↔ S.val ≤ T.val := by
  rw [← pointSet_subset_iff sigma H (isotropicSpaceImage sigma H f hf S) (isotropicSpaceImage sigma H f hf T),
    ← pointSet_subset_iff sigma H S T,
    isotropicSpaceImage_pointSet sigma H hsep, isotropicSpaceImage_pointSet sigma H hsep]
  constructor
  · intro h P hP
    obtain ⟨Q, hQ, he⟩ := h (Set.mem_image_of_mem f hP)
    exact (f.injective he) ▸ hQ
  · intro h
    exact Set.image_mono h

def isotropicSpaceOrderIso (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) : IsotropicSpace sigma H ≃o IsotropicSpace sigma H where
  toEquiv := isotropicSpaceEquiv sigma H hsep f hf
  map_rel_iff' := isotropicSpaceImage_le_iff sigma H hsep f hf _ _

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
