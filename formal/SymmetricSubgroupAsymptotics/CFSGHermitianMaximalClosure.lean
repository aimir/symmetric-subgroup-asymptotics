import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalSubspaceHom
import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicExtension

/-! Orthogonality determines the closure obtained by intersecting all
maximal isotropic point sets. Once literal maximal spaces separate the
vectors outside a given subspace, this is exactly its full point set.
This isolates the elementary separation lemma needed for line incidence;
no polar extension or semilinearity statement is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def maximalPointClosure (C : Set (SingularPoint sigma H)) : Set (SingularPoint sigma H) :=
  {P | ∀ M : {M : Submodule K (I → K) // MaximalIsotropic sigma H M},
    C ⊆ pointSet sigma H M.val → P.val ≤ M.val}

theorem subset_maximalPointClosure (C : Set (SingularPoint sigma H)) :
    C ⊆ maximalPointClosure sigma H C := by
  intro P hP M hM
  exact hM hP

theorem maximalPointClosure_image (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) (C : Set (SingularPoint sigma H))
    (P : SingularPoint sigma H) :
    f P ∈ maximalPointClosure sigma H (f '' C) ↔ P ∈ maximalPointClosure sigma H C := by
  let F := maximalIsotropicEquiv sigma H f hf
  have hinc (Q : SingularPoint sigma H)
      (M : {M : Submodule K (I → K) // MaximalIsotropic sigma H M}) :
      (f Q).val ≤ (F M).val ↔ Q.val ≤ M.val :=
    maximalIsotropicEquiv_incidence sigma H f hf M Q
  constructor
  · intro h M hCM
    apply (hinc P M).mp
    apply h (F M)
    rintro _ ⟨Q, hQ, rfl⟩
    exact (hinc Q M).mpr (hCM hQ)
  · intro h M hCM
    have hpre : C ⊆ pointSet sigma H (F.symm M).val := by
      intro Q hQ
      apply (hinc Q (F.symm M)).mp
      simpa only [F.apply_symm_apply] using hCM (Set.mem_image_of_mem f hQ)
    have hh := (hinc P (F.symm M)).mpr (h (F.symm M) hpre)
    simpa only [F.apply_symm_apply] using hh

def SeparatedByMaximal (S : Submodule K (I → K)) : Prop :=
  ∀ x ∉ S, ∃ M, MaximalIsotropic sigma H M ∧ S ≤ M ∧ x ∉ M

theorem maximalPointClosure_pointSet_eq (S : Submodule K (I → K))
    (hS : SeparatedByMaximal sigma H S) :
    maximalPointClosure sigma H (pointSet sigma H S) = pointSet sigma H S := by
  apply Set.Subset.antisymm
  · intro P hP x hx
    by_contra hxs
    obtain ⟨M, hM, hSM, hxM⟩ := hS x hxs
    exact hxM (hP ⟨M, hM⟩ (pointSet_mono sigma H hSM) hx)
  · exact subset_maximalPointClosure sigma H _

theorem maximalPointClosure_eq_pointSet_pointSpan (C : Set (SingularPoint sigma H))
    (hS : SeparatedByMaximal sigma H (pointSpan sigma H C)) :
    maximalPointClosure sigma H C = pointSet sigma H (pointSpan sigma H C) := by
  apply Set.Subset.antisymm
  · intro P hP
    rw [← maximalPointClosure_pointSet_eq sigma H (pointSpan sigma H C) hS]
    intro M hMC
    exact hP M ((clique_subset_pointSet_pointSpan sigma H C).trans hMC)
  · intro P hP M hMC
    have hspan : pointSpan sigma H C ≤ M.val := iSup_le (fun Q : C => hMC Q.property)
    exact hP.trans hspan

theorem pointSet_imageSpan_eq (f : Equiv.Perm (SingularPoint sigma H))
    (hf : PreservesOrthogonality sigma H f) (S : Submodule K (I → K))
    (hS : SeparatedByMaximal sigma H S)
    (hT : SeparatedByMaximal sigma H (pointSpan sigma H (f '' pointSet sigma H S))) :
    pointSet sigma H (pointSpan sigma H (f '' pointSet sigma H S)) = f '' pointSet sigma H S := by
  have hinc (Q : SingularPoint sigma H) :
      f Q ∈ pointSet sigma H (pointSpan sigma H (f '' pointSet sigma H S)) ↔
        Q ∈ pointSet sigma H S := by
    have hh := maximalPointClosure_image sigma H f hf (pointSet sigma H S) Q
    rw [maximalPointClosure_pointSet_eq sigma H S hS,
      maximalPointClosure_eq_pointSet_pointSpan sigma H _ hT] at hh
    exact hh
  ext P
  constructor
  · intro hP
    refine ⟨f.symm P, (hinc (f.symm P)).mp ?_, f.apply_symm_apply P⟩
    simpa only [f.apply_symm_apply] using hP
  · rintro ⟨Q, hQ, rfl⟩
    exact (hinc Q).mpr hQ

theorem preserves_pointSet_incidence_of_closure
    (f : Equiv.Perm (SingularPoint sigma H)) (hf : PreservesOrthogonality sigma H f)
    (S T : Submodule K (I → K))
    (C : Set (SingularPoint sigma H))
    (hC : maximalPointClosure sigma H C = pointSet sigma H S)
    (himage : maximalPointClosure sigma H (f '' C) = pointSet sigma H T)
    (P : SingularPoint sigma H) : (f P).val ≤ T ↔ P.val ≤ S := by
  have hh := maximalPointClosure_image sigma H f hf C P
  rw [hC, himage] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
