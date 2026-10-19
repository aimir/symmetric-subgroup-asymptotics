import SymmetricSubgroupAsymptotics.SeparatedNormalAxesQuotientSocles

/-! An actual common nontrivial normal axis is the entire socle and needs
one normal generator. The statement uses every original normal subgroup. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.MonolithicSocleOne
variable {G : Type} [Group G]

theorem minimalNormal (D : Subgroup G) [D.Normal] (hD : D≠⊥)
    (hcover : ∀ (N : Subgroup G) [N.Normal], N≠⊥ → D≤N) : IsMinimalNormalSubgroup D := by
  refine ⟨inferInstance,hD,?_⟩
  intro H hH hHne hHD
  letI : H.Normal := hH
  exact le_antisymm hHD (hcover H hHne)

theorem socle_eq (D : Subgroup G) [D.Normal] (hD : D≠⊥)
    (hcover : ∀ (N : Subgroup G) [N.Normal], N≠⊥ → D≤N) : finiteGroupSocle G=D := by
  have hminimal := minimalNormal D hD hcover
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x ⟨M,hM,hx⟩
    letI : M.Normal := hM.1
    have he : D=M := hM.2.2 D inferInstance hD (hcover M hM.2.1)
    exact he.symm ▸ hx
  · intro x hx
    exact Subgroup.subset_normalClosure ⟨D,hminimal,hx⟩

theorem normalGen_le_one (D : Subgroup G) [D.Normal] (hD : D≠⊥)
    (hcover : ∀ (N : Subgroup G) [N.Normal], N≠⊥ → D≤N) :
    MarkedC4.normalGen (finiteGroupSocle G)≤1 := by
  rw [socle_eq D hD hcover]
  exact SeparatedNormalAxesQuotientSocles.normalGen_le_one_of_minimal D (minimalNormal D hD hcover)

end SymmetricSubgroupAsymptotics.MonolithicSocleOne
