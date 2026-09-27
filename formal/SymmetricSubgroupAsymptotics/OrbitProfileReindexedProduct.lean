import SymmetricSubgroupAsymptotics.OrbitProfileProduct

/-!
# Exact physical assembly after reindexing the original product group

A literal multiplicative chart into the product of original local action
groups transports an actual subgroup family, with coordinate fullness and
an arbitrary predicate on its original permutation image. The existing
orbit-profile labelling theorem then supplies the physical count under
its naturality and action-separation hypotheses. No subgroup-cardinality
estimate or independent-coordinate premise is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.OrbitProfileReindexedProduct

variable {ι G : Type*} {Ω : ι → Type*} [Group G]
    (m : ι → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
    (e : G ≃* OrbitProfileProductGroup m U)
    (P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop)

/-- The actual permutation image of the original reindexed subgroup. -/
def image (Y : Subgroup G) : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) :=
  (Y.map e.toMonoidHom).map (orbitProfileProductAction m U)

def ModelFamily :=
  {Y : Subgroup G // OrbitProfileProductFull m U (Y.map e.toMonoidHom) ∧
    P (image m U e Y)}

def modelPredicate (K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m))) : Prop :=
  OrbitProfileFull U 1 K ∧ P K

/-- Map to and recover from the same original permutation subgroup. -/
def modelEquiv : ModelFamily m U e P ≃ {K // modelPredicate m U P K} where
  toFun Y := ⟨image m U e Y.1, orbitProfileProductFull_map Y.2.1, Y.2.2⟩
  invFun K := ⟨(K.1.comap (orbitProfileProductAction m U)).comap e.toMonoidHom, by
    have he := Subgroup.map_comap_eq_self_of_surjective
      (f := e.toMonoidHom) e.surjective (K.1.comap (orbitProfileProductAction m U))
    constructor
    · rw [he]
      exact orbitProfileFull_comap K.2.1
    · change P ((((K.1.comap (orbitProfileProductAction m U)).comap e.toMonoidHom).map
        e.toMonoidHom).map (orbitProfileProductAction m U))
      rw [he, Subgroup.map_comap_eq_self (orbitProfileFull_le_product_range K.2.1)]
      exact K.2.2⟩
  left_inv Y := by
    apply Subtype.ext
    change (((Y.1.map e.toMonoidHom).map (orbitProfileProductAction m U)).comap
      (orbitProfileProductAction m U)).comap e.toMonoidHom = Y.1
    rw [Subgroup.comap_map_eq_self_of_injective
      (f := orbitProfileProductAction m U) (orbitProfileProductAction_injective m U),
      Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective]
  right_inv K := by
    apply Subtype.ext
    change (((K.1.comap (orbitProfileProductAction m U)).comap e.toMonoidHom).map
      e.toMonoidHom).map (orbitProfileProductAction m U) = K.1
    rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
    exact Subgroup.map_comap_eq_self (orbitProfileFull_le_product_range K.2.1)

theorem card_model :
    Nat.card (ModelFamily m U e P) = Nat.card {K // modelPredicate m U P K} :=
  Nat.card_congr (modelEquiv m U e P)

/-- The predicate is transported on the entire original subgroup, not on
any quotient or independently selected coordinate images. -/
theorem modelEquiv_original (Y : ModelFamily m U e P) :
    (modelEquiv m U e P Y).1 = image m U e Y.1 := rfl

section Physical

variable [Fintype ι] [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]

theorem modelPredicate_natural (hP : OrbitProfileFamilyNatural Ω m U P) :
    OrbitProfileFamilyNatural Ω m U (modelPredicate m U P) := by
  intro w hw K hK
  exact ⟨orbitProfileFull_family_natural m U w hw K hK.1, hP w hw K hK.2⟩

abbrev PhysicalFamily (X : Type*) := AssembledOrbitProfileOn (modelPredicate m U P) X

/-- Exact count of the natural whole profile, with every original local
normalizer and every occurrence factorial unchanged. -/
theorem card_physical_rat {X : Type*} (chart : OrbitProfilePoints Ω m ≃ X)
    (hP : OrbitProfileFamilyNatural Ω m U P)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    (Nat.card (PhysicalFamily m U P X) : ℚ) =
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℚ) *
        Nat.card (ModelFamily m U e P) /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℚ) ^ m i *
          (m i).factorial) := by
  have h := assembledOrbitProfileOn_card_rat chart
    (fun K (hK : modelPredicate m U P K) => hK.1)
    (modelPredicate_natural m U P hP) htrans hsep
  rw [← card_model m U e P] at h
  exact h

end Physical

end SymmetricSubgroupAsymptotics.OrbitProfileReindexedProduct

end
