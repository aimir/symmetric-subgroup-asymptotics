import SymmetricSubgroupAsymptotics.FusionGoursatCount

/-! Literal epi transport along actual source and quotient isomorphisms. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {J K Q R G : Type*} [Group J] [Group K] [Group Q] [Group R] [Group G]

/-- Transport every literal map; onto maps remain onto and are recovered. -/
def fusionGroupEpimorphismCongr (e : J ≃* K) (f : Q ≃* R) :
    GroupEpimorphism J Q ≃ GroupEpimorphism K R where
  toFun β := ⟨(f.toMonoidHom.comp β.1).comp e.symm.toMonoidHom,
    f.surjective.comp (β.2.comp e.symm.surjective)⟩
  invFun β := ⟨(f.symm.toMonoidHom.comp β.1).comp e.toMonoidHom,
    f.symm.surjective.comp (β.2.comp e.surjective)⟩
  left_inv β := by apply Subtype.ext; ext j; simp
  right_inv β := by apply Subtype.ext; ext k; simp

theorem fusionGroupEpimorphism_card_congr (e : J ≃* K) (f : Q ≃* R) :
    Nat.card (GroupEpimorphism J Q)=Nat.card (GroupEpimorphism K R) :=
  Nat.card_congr (fusionGroupEpimorphismCongr e f)

/-- The complete-source epi count is invariant under any actual ambient
coordinate change. This can justify a conjugacy-invariant moment envelope. -/
theorem fusionGroupEpimorphism_card_map (e : G ≃* G) (J : Subgroup G) :
    Nat.card (GroupEpimorphism (J.map e.toMonoidHom) Q) =
      Nat.card (GroupEpimorphism J Q) :=
  (fusionGroupEpimorphism_card_congr (e.subgroupMap J) (MulEquiv.refl Q)).symm

end SymmetricSubgroupAsymptotics
