import SymmetricSubgroupAsymptotics.CosetProjectionFibreCard

/-! Index transport for the actual inclusion of a local Borel power.
Every projection fibre retains the original correlated subgroup H. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.InjectiveCosetProjectionFibreIndex
variable {A G : Type*} [Group A] [Group G]

theorem mapped_subgroup_relindex (f : A →* G) (hf : Function.Injective f) (H : Subgroup A) :
    ((H.map f).subgroupOf f.range).index=H.index := by
  let e : A ≃* f.range := MonoidHom.ofInjective hf
  have heq : (H.map f).subgroupOf f.range=H.map e.toMonoidHom := by
    ext b
    constructor
    · rintro ⟨a,ha,hab⟩
      refine ⟨a,ha,?_⟩
      exact Subtype.ext hab
    · rintro ⟨a,ha,hab⟩
      exact ⟨a,ha,congrArg Subtype.val hab⟩
  rw [heq]
  exact H.index_map_equiv e

/-- Every fibre is B/H, even when H is correlated and not normal in G. -/
theorem card_fibre_eq_index (f : A →* G) (hf : Function.Injective f)
    (H : Subgroup A) (q : G ⧸ f.range) :
    Nat.card {x : G ⧸ H.map f //
      Subgroup.quotientMapOfLE (show H.map f ≤ f.range from by
        rintro _ ⟨a,_,rfl⟩; exact ⟨a,rfl⟩) x=q} = H.index := by
  exact (CosetProjectionFibreCard.card_fibre _ _ _ q).trans
    (mapped_subgroup_relindex f hf H)

end SymmetricSubgroupAsymptotics.InjectiveCosetProjectionFibreIndex
