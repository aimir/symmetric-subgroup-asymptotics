import SymmetricSubgroupAsymptotics.CFSGSylowCenterConjugacy

/-! The family of whole Sylow-centre subgroups is intrinsic, not just
the union of their elements. This generic fact will be applied to the
proved literal D Sylow and its exact highest-root centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylowCenterFamily
variable {G : Type*} [Group G]

def centerImage (H : Subgroup G) : Subgroup G :=
  (Subgroup.center H).map H.subtype

theorem map_centerImage (f : MulAut G) (H : Subgroup G) :
    (centerImage H).map f.toMonoidHom = centerImage (H.map f.toMonoidHom) := by
  let e : H ≃* H.map f.toMonoidHom := f.subgroupMap H
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨e z, (Subgroup.centerCongr e ⟨z, hz⟩).property, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    let z : Subgroup.center H := (Subgroup.centerCongr e).symm ⟨w, hw⟩
    refine ⟨z.val, ⟨z.val, z.property, rfl⟩, ?_⟩
    have he := congrArg (fun v : Subgroup.center (H.map f.toMonoidHom) =>
      ((v.val : H.map f.toMonoidHom) : G))
        ((Subgroup.centerCongr e).apply_symm_apply ⟨w, hw⟩)
    exact he

theorem exists_inner_centerImage_map [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (f : MulAut G) :
    ∃ g : G, (centerImage (P : Subgroup G)).map f.toMonoidHom =
      (centerImage (P : Subgroup G)).map (MulAut.conj g).toMonoidHom := by
  let Q : Sylow p G := P.mapSurjective (f := f.toMonoidHom) f.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have he : (P : Subgroup G).map f.toMonoidHom =
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun R : Sylow p G => (R : Subgroup G)) hg
    change MulAut.conj g • (P : Subgroup G) = (P : Subgroup G).map f.toMonoidHom at h
    rw [Subgroup.pointwise_smul_def] at h
    exact h.symm
  refine ⟨g, ?_⟩
  rw [map_centerImage, map_centerImage, he]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylowCenterFamily
