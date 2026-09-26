import SymmetricSubgroupAsymptotics.BinaryTransport

/-! Coordinatewise epimorphisms lift full original families into full
cover families. The whole critical or exterior product is left untouched;
its projection may be proper. Literal image reconstruction preserves every
original predicate and any scalar original profile weight.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CarrierEpimorphismPullback

variable {ι : Type*} {A B : ι → Type*} {E : Type*}
    [∀ i, Group (A i)] [∀ i, Group (B i)] [Group E]

/-- Individual carrier fullness, with no fullness requirement on E. -/
def CoordinateFull (H : Subgroup (E × (∀ i, A i))) : Prop :=
  ∀ i (a : A i), ∃ h : H, h.1.2 i = a

variable (β : ∀ i, B i →* A i)

/-- The untouched exterior coordinate is literally the identity map. -/
def productMap : (E × (∀ i, B i)) →* (E × (∀ i, A i)) :=
  (MonoidHom.id E).prodMap (carrierProductMap β)

@[simp] theorem productMap_apply (x : E) (b : ∀ i, B i) :
    productMap β (x,b) = (x,fun i => β i (b i)) := rfl

theorem productMap_surjective (hβ : ∀ i, Function.Surjective (β i)) :
    Function.Surjective (productMap (E := E) β) := by
  rintro ⟨x,a⟩
  obtain ⟨b,hb⟩ := carrierProductMap_surjective β hβ a
  exact ⟨(x,b),Prod.ext rfl hb⟩

def pullback (H : Subgroup (E × (∀ i, A i))) :
    Subgroup (E × (∀ i, B i)) := H.comap (productMap β)

/-- Recover the complete original subgroup, without an original-axis or
kernel-containment assumption. -/
theorem reconstruct (hβ : ∀ i, Function.Surjective (β i))
    (H : Subgroup (E × (∀ i, A i))) :
    (pullback β H).map (productMap β) = H :=
  Subgroup.map_comap_eq_self_of_surjective (productMap_surjective β hβ) H

/-- Every relation and every individual critical projection inside the
untouched exterior has exactly the same image as before. -/
theorem exterior_image (hβ : ∀ i, Function.Surjective (β i))
    (H : Subgroup (E × (∀ i, A i))) :
    (pullback β H).map (MonoidHom.fst E (∀ i, B i)) =
      H.map (MonoidHom.fst E (∀ i, A i)) := by
  calc
    _ = ((pullback β H).map (productMap β)).map
        (MonoidHom.fst E (∀ i, A i)) := by
      rw [Subgroup.map_map]
      rfl
    _ = _ := by rw [reconstruct β hβ H]

/-- Surjectivity permits simultaneous lifts, with the chosen carrier
coordinate fixed to any prescribed element of its complete cover group. -/
theorem coordinateFull_pullback (hβ : ∀ i, Function.Surjective (β i))
    (H : Subgroup (E × (∀ i, A i))) (hH : CoordinateFull H) :
    CoordinateFull (pullback β H) := by
  classical
  intro i b
  obtain ⟨x,hx⟩ := hH i (β i b)
  choose d hd using fun j => hβ j (x.1.2 j)
  have he : productMap β (x.1.1,Function.update d i b) = x.1 := by
    apply Prod.ext
    · rfl
    · funext j
      change β j ((Function.update d i b) j) = x.1.2 j
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self] using hx.symm
      · simpa only [Function.update_of_ne hj] using hd j
  refine ⟨⟨(x.1.1,Function.update d i b),?_⟩,?_⟩
  · change productMap β (x.1.1,Function.update d i b) ∈ H
    rw [he]
    exact x.2
  · change Function.update d i b i = b
    exact Function.update_self i b d

theorem coordinateFull_pullback_iff (hβ : ∀ i, Function.Surjective (β i))
    (H : Subgroup (E × (∀ i, A i))) :
    CoordinateFull (pullback β H) ↔ CoordinateFull H := by
  constructor
  · intro h i a
    obtain ⟨b,hb⟩ := hβ i a
    obtain ⟨x,hx⟩ := h i b
    refine ⟨⟨productMap β x.1,x.2⟩,?_⟩
    change β i (x.1.2 i) = a
    rw [hx,hb]
  · exact coordinateFull_pullback β hβ H

/-- Q can retain all individual critical/exterior fullness conditions.
P can depend jointly on the complete original subgroup. -/
abbrev OriginalFamily (Q : Subgroup E → Prop)
    (P : Subgroup (E × (∀ i, A i)) → Prop) :=
  {H : Subgroup (E × (∀ i, A i)) //
    CoordinateFull H ∧ Q (H.map (MonoidHom.fst E (∀ i, A i))) ∧ P H}

abbrev CoverFamily (Q : Subgroup E → Prop)
    (P : Subgroup (E × (∀ i, A i)) → Prop) :=
  {K : Subgroup (E × (∀ i, B i)) //
    CoordinateFull K ∧ Q (K.map (MonoidHom.fst E (∀ i, B i))) ∧
      P (K.map (productMap β))}

/-- The target may contain additional full cover subgroups; the original
family still embeds because the image reconstructs its literal subgroup. -/
def familyEmbedding (hβ : ∀ i, Function.Surjective (β i))
    (Q : Subgroup E → Prop) (P : Subgroup (E × (∀ i, A i)) → Prop) :
    OriginalFamily Q P ↪ CoverFamily β Q P where
  toFun H := ⟨pullback β H.1,coordinateFull_pullback β hβ H.1 H.2.1,by
      rw [exterior_image β hβ H.1]
      exact H.2.2.1,by
      rw [reconstruct β hβ H.1]
      exact H.2.2.2⟩
  inj' := by
    intro H K h
    have he : pullback β H.1 = pullback β K.1 :=
      congrArg (fun J : CoverFamily β Q P => J.1) h
    apply Subtype.ext
    have hi := congrArg (fun J : Subgroup (E × (∀ i, B i)) => J.map (productMap β)) he
    simpa only [reconstruct β hβ H.1,reconstruct β hβ K.1] using hi

theorem familyEmbedding_reconstruct (hβ : ∀ i, Function.Surjective (β i))
    (Q : Subgroup E → Prop) (P : Subgroup (E × (∀ i, A i)) → Prop)
    (H : OriginalFamily Q P) :
    (familyEmbedding β hβ Q P H).1.map (productMap β) = H.1 :=
  reconstruct β hβ H.1

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

theorem family_card_le [Finite ι] [Finite E] [∀ i, Finite (B i)]
    (hβ : ∀ i, Function.Surjective (β i))
    (Q : Subgroup E → Prop) (P : Subgroup (E × (∀ i, A i)) → Prop) :
    Nat.card (OriginalFamily Q P) ≤ Nat.card (CoverFamily β Q P) :=
  Nat.card_le_card_of_injective (familyEmbedding β hβ Q P) (familyEmbedding β hβ Q P).injective

/-- Any fixed original physical-profile scalar is retained on both sides.
There is no division by a cover action normalizer or by an automorphism group. -/
theorem original_weight_le [Finite ι] [Finite E] [∀ i, Finite (B i)]
    (hβ : ∀ i, Function.Surjective (β i))
    (Q : Subgroup E → Prop) (P : Subgroup (E × (∀ i, A i)) → Prop)
    (weight : ℝ) (hweight : 0 ≤ weight) :
    weight * (Nat.card (OriginalFamily Q P) : ℝ) ≤
      weight * (Nat.card (CoverFamily β Q P) : ℝ) := by
  apply mul_le_mul_of_nonneg_left _ hweight
  exact_mod_cast family_card_le β hβ Q P

end SymmetricSubgroupAsymptotics.CarrierEpimorphismPullback
