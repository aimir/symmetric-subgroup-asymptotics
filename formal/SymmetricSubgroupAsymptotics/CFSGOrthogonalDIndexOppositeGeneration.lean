import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeCoverage

/-! The SAME literal D-unipotent subgroup and its conjugate by the
original Coxeter word generate the original elementary group. Every
membership transfer uses the actual subtype homomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeGeneration
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDIndexUnipotent CFSGOrthogonalDIndexOppositeRootLines
open CFSGOrthogonalDIndexOppositeCoverage
variable (K : Type) [Field K]

theorem two_unipotents_generate (s : ℕ) :
    Subgroup.closure ((unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))) ∪
      (unipotent K (s + 4)).map (MulAut.conj (coxeterWeyl K (s + 3))).toMonoidHom) = ⊤ := by
  let W := coxeterWeyl K (s + 3)
  let H := Subgroup.closure ((unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))) ∪
    (unipotent K (s + 4)).map (MulAut.conj W).toMonoidHom)
  have hU : unipotent K (s + 4) ≤ H := by
    intro u hu
    exact Subgroup.subset_closure (Or.inl hu)
  have hWU : (unipotent K (s + 4)).map (MulAut.conj W).toMonoidHom ≤ H := by
    intro u hu
    exact Subgroup.subset_closure (Or.inr hu)
  let A := H.map (elementaryRootGroup K (s + 4)).subtype
  have haU : ambientUnipotent K (s + 4) ≤ A := by
    rintro g ⟨u, hu, rfl⟩
    exact ⟨u, hU hu, rfl⟩
  have haWU : (ambientUnipotent K (s + 4)).map
      (MulAut.conj W.val).toMonoidHom ≤ A := by
    rintro g ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨W * u * W⁻¹, hWU ⟨u, hu, rfl⟩, rfl⟩
  have he := elementary_le_of_U_and_coxeter_U K s A haU haWU
  apply top_unique
  intro g _
  obtain ⟨h, hh, heq⟩ := he g.property
  exact (Subtype.val_injective heq) ▸ hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOppositeGeneration
