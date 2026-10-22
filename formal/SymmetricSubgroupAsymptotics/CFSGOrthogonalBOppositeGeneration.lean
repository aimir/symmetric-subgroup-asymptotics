import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOppositeRootLines

/-! Two literal conjugate flag-unitriangular subgroups generate the
original natural B elementary group. No abstract opposite-Borel or
orthogonal-group generation premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
open CFSGOrthogonalBGenerationElements
variable (K : Type) [Field K]

theorem two_unipotents_generate (r : ℕ) :
    Subgroup.closure ((unipotent K (r+1) : Set (elementaryRootGroup K (r+1))) ∪
      (unipotent K (r+1)).map (MulAut.conj (opposition K r)).toMonoidHom) = ⊤ := by
  apply top_unique
  rw [← rootElements_generate K (r+1)]
  apply Subgroup.closure_mono
  rintro x ⟨neg,i,a,rfl⟩
  cases neg with
  | false => exact Or.inl (positive_mem_unipotent K r i a)
  | true =>
    refine Or.inr ⟨rootElement K (r+1) false i (rootScale K r i*a),
      positive_mem_unipotent K r i _, ?_⟩
    have he : rootScale K r i*(rootScale K r i*a)=a := by
      rw [← mul_assoc, rootScale_square, one_mul]
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, he]
      using opposition_conjugates_positive K r i (rootScale K r i*a)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
