import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan

/-! An orthogonality-preserving permutation of the literal singular
point lines acts on every maximal totally isotropic subspace. Point
incidence is recovered exactly; no semilinear realization is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def PreservesOrthogonality (f : Equiv.Perm (SingularPoint sigma H)) : Prop :=
  ∀ P Q, Orthogonal sigma H (f P).val (f Q).val ↔ Orthogonal sigma H P.val Q.val

theorem preservesOrthogonality_symm (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) : PreservesOrthogonality sigma H f.symm := by
  intro P Q
  simpa only [f.apply_symm_apply] using (hf (f.symm P) (f.symm Q)).symm

theorem image_isClique (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f)
    {C : Set (SingularPoint sigma H)} (hC : IsClique sigma H C) :
    IsClique sigma H (f '' C) := by
  rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩
  exact (hf P Q).mpr (hC P hP Q hQ)

theorem image_maximalClique (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f)
    {C : Set (SingularPoint sigma H)} (hC : MaximalClique sigma H C) :
    MaximalClique sigma H (f '' C) := by
  refine ⟨image_isClique sigma H f hf hC.1, ?_⟩
  intro D hD hCD
  have hpre : IsClique sigma H (f ⁻¹' D) := by
    intro P hP Q hQ
    exact (hf P Q).mp (hD (f P) hP (f Q) hQ)
  have he : f ⁻¹' D = C := hC.2 _ hpre (by
    intro P hP
    exact hCD (Set.mem_image_of_mem f hP))
  apply Set.Subset.antisymm
  · intro P hP
    have hx : f.symm P ∈ f ⁻¹' D := by
      change f (f.symm P) ∈ D
      rwa [f.apply_symm_apply]
    refine ⟨f.symm P, ?_, f.apply_symm_apply P⟩
    rwa [he] at hx
  · exact hCD

def maximalIsotropicMap (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f)
    (S : {S : Submodule K (I → K) // MaximalIsotropic sigma H S}) :
    {S : Submodule K (I → K) // MaximalIsotropic sigma H S} :=
  ⟨pointSpan sigma H (f '' pointSet sigma H S.val),
    (maximalClique_pointSpan sigma H
      (image_maximalClique sigma H f hf (maximalIsotropic_pointSet sigma H S.property))).1⟩

theorem maximalIsotropicMap_pointSet (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f)
    (S : {S : Submodule K (I → K) // MaximalIsotropic sigma H S}) :
    pointSet sigma H (maximalIsotropicMap sigma H f hf S).val = f '' pointSet sigma H S.val :=
  (maximalClique_pointSpan sigma H
    (image_maximalClique sigma H f hf (maximalIsotropic_pointSet sigma H S.property))).2

theorem maximalIsotropicMap_symm (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f)
    (S : {S : Submodule K (I → K) // MaximalIsotropic sigma H S}) :
    maximalIsotropicMap sigma H f.symm (preservesOrthogonality_symm sigma H f hf)
      (maximalIsotropicMap sigma H f hf S) = S := by
  apply Subtype.ext
  change pointSpan sigma H (f.symm '' pointSet sigma H
    (maximalIsotropicMap sigma H f hf S).val) = S.val
  rw [maximalIsotropicMap_pointSet]
  have he : f.symm '' (f '' pointSet sigma H S.val) = pointSet sigma H S.val := by
    ext P
    constructor
    · rintro ⟨_, ⟨Q, hQ, rfl⟩, he⟩
      rw [f.symm_apply_apply] at he
      exact he ▸ hQ
    · intro hP
      exact ⟨f P, Set.mem_image_of_mem f hP, f.symm_apply_apply P⟩
  rw [he, pointSpan_pointSet_eq sigma H S.val S.property.1]

def maximalIsotropicEquiv (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) :
    Equiv.Perm {S : Submodule K (I → K) // MaximalIsotropic sigma H S} where
  toFun := maximalIsotropicMap sigma H f hf
  invFun := maximalIsotropicMap sigma H f.symm (preservesOrthogonality_symm sigma H f hf)
  left_inv := maximalIsotropicMap_symm sigma H f hf
  right_inv := by
    intro S
    simpa only [Equiv.symm_symm] using maximalIsotropicMap_symm sigma H f.symm
      (preservesOrthogonality_symm sigma H f hf) S

theorem maximalIsotropicEquiv_incidence (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f)
    (S : {S : Submodule K (I → K) // MaximalIsotropic sigma H S})
    (P : SingularPoint sigma H) :
    (f P).val ≤ (maximalIsotropicEquiv sigma H f hf S).val ↔ P.val ≤ S.val := by
  change f P ∈ pointSet sigma H (maximalIsotropicMap sigma H f hf S).val ↔
    P ∈ pointSet sigma H S.val
  rw [maximalIsotropicMap_pointSet]
  constructor
  · rintro ⟨Q, hQ, he⟩
    exact (f.injective he) ▸ hQ
  · intro hP
    exact Set.mem_image_of_mem f hP

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
