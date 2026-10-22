import SymmetricSubgroupAsymptotics.CFSGPolarLocalFieldCoherence

/-! Extracting a literal common plane from the actual intersection
dimension, for applying the proved semilinear field-coherence theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_common_plane (W Z : Submodule K V)
    (h : 2≤Module.finrank K (W⊓Z : Submodule K V)) :
    ∃T : Submodule K V,Module.finrank K T=2 ∧ T≤W ∧ T≤Z := by
  let N : Submodule K V := W⊓Z
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank h
  let L : Submodule K N := Submodule.span K (Set.range v)
  have hdL : Module.finrank K L=2 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hv
  let T := L.map N.subtype
  have hdT : Module.finrank K T=2 := (Submodule.finrank_map_subtype_eq N L).trans hdL
  have hTN : T≤N := by
    rintro x ⟨z,_,rfl⟩
    exact z.property
  exact ⟨T,hdT,hTN.trans inf_le_left,hTN.trans inf_le_right⟩

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
