import SymmetricSubgroupAsymptotics.CFSGNilpotentSupportRestriction
import SymmetricSubgroupAsymptotics.CFSGPermutationOrbitRestriction

/-! Delete actual fixed points WITHOUT discarding the nilpotent orbit
cutoff. Thus only fixed-cutoff nilpotent counting is needed for the ordinary
upper theorem; no global nilpotent counting theorem is a prerequisite. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGNilpotentBoundedSupportRestriction
open MarkedC4 CFSGOrdinaryLargeOrbitDegree CFSGPermutationOrbitRestriction

abbrev BoundedNilpotent (C : ℕ) (X : Type) :=
  {J : Subgroup (Equiv.Perm X) // Group.IsNilpotent J ∧
    ∀ x : X,Nat.card (MulAction.orbit J x)<C}
abbrev BoundedNilpotentFixedTargets (C b m : ℕ) :=
  {J : Subgroup (PermutationGroup b) // Group.IsNilpotent J ∧
    OrbitCutoffFamilies.OrbitCutoff C J ∧ FixedPointsWitness b m J}

private theorem mem_extension_range_of_fixes {A B : Type} (i : A ↪ B) (p : Equiv.Perm B)
    (hfix : ∀ x,x∉Set.range i → p x=x) : p∈(Equiv.Perm.viaEmbeddingHom i).range := by
  have hpreserve : ∀ x,p x∈Set.range i ↔ x∈Set.range i := by
    intro x
    constructor
    · intro hx
      by_contra hn
      exact hn ((hfix x hn) ▸ hx)
    · intro hx
      by_contra hn
      have hp := hfix (p x) hn
      have he : p x=x := p.injective hp
      exact hn (he.symm ▸ hx)
  let e : A ≃ Set.range i := Equiv.ofInjective i i.injective
  let q : Equiv.Perm A := e.symm.permCongr (p.subtypePerm hpreserve)
  refine ⟨q,?_⟩
  apply Equiv.ext
  intro x
  by_cases hx : x∈Set.range i
  · obtain ⟨a,rfl⟩ := hx
    rw [Equiv.Perm.viaEmbeddingHom_apply,Equiv.Perm.viaEmbedding_apply]
    exact congrArg Subtype.val (e.apply_symm_apply (p.subtypePerm hpreserve (e a)))
  · rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,hfix x hx]

theorem supported_bounded_card_le {C : ℕ} {X : Type} [Finite X] (T : Set X) :
    Nat.card {J : Subgroup (Equiv.Perm X) // Group.IsNilpotent J ∧
      (∀ x : X,Nat.card (MulAction.orbit J x)<C) ∧ ∀ x∈T,∀ g∈J,g x=x} ≤
      Nat.card (BoundedNilpotent C ↥(Tᶜ)) := by
  let A := {J : Subgroup (Equiv.Perm X) // Group.IsNilpotent J ∧
    (∀ x : X,Nat.card (MulAction.orbit J x)<C) ∧ ∀ x∈T,∀ g∈J,g x=x}
  let i : ↥(Tᶜ) ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  let f := Equiv.Perm.viaEmbeddingHom i
  have hrange (J : A) : J.val≤f.range := by
    intro g hg
    apply mem_extension_range_of_fixes i g
    intro x hx
    apply J.property.2.2 x
    · by_contra hn
      exact hx ⟨⟨x,hn⟩,rfl⟩
    · exact hg
  have hn (J : A) : Group.IsNilpotent (J.val.comap f) := by
    letI := J.property.1
    let e : J.val.comap f ≃* J.val :=
      ((J.val.comap f).equivMapOfInjective f (Equiv.Perm.viaEmbeddingHom_injective i)).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (hrange J)))
    exact Group.nilpotent_of_mulEquiv e.symm
  have hcut (J : A) (x : ↥(Tᶜ)) : Nat.card (MulAction.orbit (J.val.comap f) x)<C := by
    let lift : J.val.comap f → J.val := fun g => ⟨f g.val,g.property⟩
    apply (orbit_card_le_of_embedding (J.val.comap f) J.val i lift (by
      intro g y
      change i (g.val y)=(g.val.viaEmbedding i) (i y)
      exact (Equiv.Perm.viaEmbedding_apply g.val i y).symm) x).trans_lt
    exact J.property.2.1 (i x)
  let code : A → BoundedNilpotent C ↥(Tᶜ) := fun J => ⟨J.val.comap f,hn J,hcut J⟩
  apply Nat.card_le_card_of_injective code
  intro J L h
  apply Subtype.ext
  have he := congrArg (fun R : Subgroup (Equiv.Perm ↥(Tᶜ)) => R.map f) (congrArg Subtype.val h)
  change (J.val.comap f).map f=(L.val.comap f).map f at he
  simpa only [Subgroup.map_comap_eq_self (hrange J),Subgroup.map_comap_eq_self (hrange L)] using he

theorem bounded_card_eq_of_equiv {C : ℕ} {X Y : Type} [Finite X] [Finite Y] (e : X ≃ Y) :
    Nat.card (BoundedNilpotent C X)=Nat.card (BoundedNilpotent C Y) := by
  have hle {A B : Type} [Finite A] [Finite B] (d : A ≃ B) :
      Nat.card (BoundedNilpotent C A)≤Nat.card (BoundedNilpotent C B) := by
    let f := d.permCongrHom.toMonoidHom
    have hf : Function.Injective f := d.permCongrHom.injective
    have hn (J : BoundedNilpotent C A) : Group.IsNilpotent (J.val.map f) := by
      letI := J.property.1
      exact Group.nilpotent_of_mulEquiv (J.val.equivMapOfInjective f hf)
    let code : BoundedNilpotent C A → BoundedNilpotent C B :=
      fun J => ⟨J.val.map f,hn J,cutoff_map_equiv J.val d J.property.2⟩
    apply Nat.card_le_card_of_injective code
    intro J K h
    apply Subtype.ext
    exact Subgroup.map_injective hf (congrArg Subtype.val h)
  exact Nat.le_antisymm (hle e) (hle e.symm)

/-- Support-sensitive bounded nilpotent counts lose only the original
fixed-point-set choice, never a full degree or an unrestricted odd count. -/
theorem bounded_fixed_card_le (C b m : ℕ) :
    Nat.card (BoundedNilpotentFixedTargets C b m) ≤
      2^b * Nat.card (OrbitCutoffFamilies.NilpotentFamily C (b-m)) := by
  let I := {T : Set (Fin b) // Nat.card T=m}
  letI : Fintype I := Fintype.ofFinite _
  let P (T : I) := {J : Subgroup (PermutationGroup b) // Group.IsNilpotent J ∧
    OrbitCutoffFamilies.OrbitCutoff C J ∧ ∀ x∈T.val,∀ g∈J,g x=x}
  have hex (J : BoundedNilpotentFixedTargets C b m) :
      ∃ T : I,∀ x∈T.val,∀ g∈J.val,g x=x := by
    obtain ⟨T,hT,hfix⟩ := J.property.2.2
    exact ⟨⟨T,hT⟩,hfix⟩
  choose fixed hfixed using hex
  let code : BoundedNilpotentFixedTargets C b m → Σ T : I,P T :=
    fun J => ⟨fixed J,⟨J.val,J.property.1,J.property.2.1,hfixed J⟩⟩
  have hinj : Function.Injective code := by
    intro J K h
    apply Subtype.ext
    exact congrArg (fun z : Σ T : I,P T => z.2.val) h
  have hlocal (T : I) : Nat.card (P T)≤Nat.card (OrbitCutoffFamilies.NilpotentFamily C (b-m)) := by
    letI : Fintype ↥(T.valᶜ) := Fintype.ofFinite _
    letI : Fintype T.val := Fintype.ofFinite _
    have hc : Fintype.card ↥(T.valᶜ)=b-m := by
      rw [Fintype.card_compl_set]
      simpa only [Fintype.card_fin,Nat.card_eq_fintype_card] using congrArg (fun a : ℕ => b-a) T.property
    let e : ↥(T.valᶜ) ≃ Fin (b-m) :=
      (Fintype.equivFin ↥(T.valᶜ)).trans (Equiv.cast (congrArg Fin hc))
    exact (supported_bounded_card_le T.val).trans_eq (bounded_card_eq_of_equiv e)
  have hI : Nat.card I≤2^b := by
    have h := Nat.card_le_card_of_injective (fun T : I => T.val) Subtype.val_injective
    simpa only [Nat.card_eq_fintype_card,Fintype.card_set,Fintype.card_fin] using h
  calc
    _ ≤ Nat.card (Σ T : I,P T) := Nat.card_le_card_of_injective code hinj
    _ = ∑ T : I,Nat.card (P T) := Nat.card_sigma
    _ ≤ ∑ _T : I,Nat.card (OrbitCutoffFamilies.NilpotentFamily C (b-m)) :=
      Finset.sum_le_sum (fun T _ => hlocal T)
    _ = Nat.card I*Nat.card (OrbitCutoffFamilies.NilpotentFamily C (b-m)) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ _ := Nat.mul_le_mul_right _ hI

end SymmetricSubgroupAsymptotics.CFSGNilpotentBoundedSupportRestriction
