import SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements

/-! Exact intersection transport through a central quotient, using proved
separation of all p-elements. Separate injectivity on the two subgroups
alone is not substituted for this separation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralKernelPIntersectionMap
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

theorem map_inf (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G)
    (U V : Subgroup G) (hU : IsPGroup p U) (hV : IsPGroup p V) :
    (U⊓V).map f=U.map f⊓V.map f := by
  apply le_antisymm
  · exact le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)
  · rintro g ⟨⟨u,hu,rfl⟩,v,hv,he⟩
    obtain ⟨a,ha⟩ := hU ⟨u,hu⟩
    obtain ⟨b,hb⟩ := hV ⟨v,hv⟩
    have huv : u=v := CFSGCentralKernelPElements.eq_of_p_elements f P hP hker u v
      ⟨a,congrArg Subtype.val ha⟩ ⟨b,congrArg Subtype.val hb⟩ he.symm
    exact ⟨u,⟨hu,huv.symm ▸ hv⟩,rfl⟩

end SymmetricSubgroupAsymptotics.CentralKernelPIntersectionMap
