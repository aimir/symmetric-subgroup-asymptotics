import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightCanonicalComplements

/-! The degree-eight branch of the original fixed small-affine catalogue
is now a theorem. One remaining classification parameter suffices for the
other two degrees; no representative facts or new correspondence fields are
introduced. The equivalence below records the exact narrowed boundary. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace SmallAffineCatalogueDegreeEightConsequences

/-- Exactly the original fixed-row locator restricted to degrees16 and27. -/
def PublishedRemainingClassification : Prop :=
  ∀ {G Ω : Type} [Group G] [Finite G] [Fintype Ω]
    [MulAction G Ω] [FaithfulSMul G Ω],
    MulAction.IsPreprimitive G Ω →
    (P : PrimitiveAffineProfile G Ω) → (x : Ω) →
    (Nat.card Ω = 16 ∨ Nat.card Ω = 27) →
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card Ω ∧
      Nonempty (P.complement x ≃*
        (SmallAffineCanonicalRepresentatives.representative r).Carrier)

theorem remaining_of_published
    (h : SmallAffineCanonicalRepresentatives.PublishedClassification) :
    PublishedRemainingClassification := by
  intro G Ω _ _ _ _ _ hprimitive P x hdegree
  exact h hprimitive P x (Or.inr hdegree)

theorem published_of_remaining (h : PublishedRemainingClassification) :
    SmallAffineCanonicalRepresentatives.PublishedClassification := by
  intro G Ω _ _ _ _ _ hprimitive P x hdegree
  rcases hdegree with h8 | h16 | h27
  · letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by rw [h8]; decide)
    exact PrimitiveAffineDegreeEightCanonicalComplements.catalogue_locator P hprimitive x h8
  · exact h hprimitive P x (Or.inl h16)
  · exact h hprimitive P x (Or.inr h27)

theorem published_iff_remaining :
    SmallAffineCanonicalRepresentatives.PublishedClassification ↔
      PublishedRemainingClassification :=
  ⟨remaining_of_published, published_of_remaining⟩

end SmallAffineCatalogueDegreeEightConsequences
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

end
