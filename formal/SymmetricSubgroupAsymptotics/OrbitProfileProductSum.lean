import SymmetricSubgroupAsymptotics.OrbitProfileProduct

/-! Splitting two classes of original orbit occurrences preserves literal
coordinate fullness and arbitrary predicates on the whole subgroup. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.OrbitProfileProductSum

variable {ι κ : Type*} {Ω : ι ⊕ κ → Type*}
    (m : ι ⊕ κ → ℕ) (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))

abbrev Left := OrbitProfileProductGroup (fun i => m (.inl i)) (fun i => U (.inl i))
abbrev Right := OrbitProfileProductGroup (fun i => m (.inr i)) (fun i => U (.inr i))

/-- Restrict to the two original color classes, keeping every occurrence. -/
def equiv : OrbitProfileProductGroup m U ≃* (Left m U × Right m U) where
  toFun f := (fun i => f (.inl i), fun i => f (.inr i))
  invFun f := fun i => match i with
    | .inl j => f.1 j
    | .inr j => f.2 j
  left_inv f := by funext i; cases i <;> rfl
  right_inv f := rfl
  map_mul' _ _ := rfl

def leftProjection : OrbitProfileProductGroup m U →* Left m U :=
  (MonoidHom.fst _ _).comp (equiv m U).toMonoidHom

def rightProjection : OrbitProfileProductGroup m U →* Right m U :=
  (MonoidHom.snd _ _).comp (equiv m U).toMonoidHom

def SplitFull (K : Subgroup (Left m U × Right m U)) : Prop :=
  OrbitProfileProductFull (fun i => m (.inl i)) (fun i => U (.inl i))
      (K.map (MonoidHom.fst _ _)) ∧
    OrbitProfileProductFull (fun i => m (.inr i)) (fun i => U (.inr i))
      (K.map (MonoidHom.snd _ _))

theorem full_iff_projection_full (K : Subgroup (OrbitProfileProductGroup m U)) :
    OrbitProfileProductFull m U K ↔
      OrbitProfileProductFull (fun i => m (.inl i)) (fun i => U (.inl i))
          (K.map (leftProjection m U)) ∧
        OrbitProfileProductFull (fun i => m (.inr i)) (fun i => U (.inr i))
          (K.map (rightProjection m U)) := by
  constructor
  · intro h
    constructor
    · intro i j u
      obtain ⟨x,hx⟩ := h (.inl i) j u
      exact ⟨⟨leftProjection m U x.1,Subgroup.mem_map.mpr ⟨x.1,x.2,rfl⟩⟩,hx⟩
    · intro i j u
      obtain ⟨x,hx⟩ := h (.inr i) j u
      exact ⟨⟨rightProjection m U x.1,Subgroup.mem_map.mpr ⟨x.1,x.2,rfl⟩⟩,hx⟩
  · rintro ⟨hl,hr⟩ i j u
    cases i with
    | inl i =>
      obtain ⟨y,hy⟩ := hl i j u
      obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x,hx⟩,(congrArg (fun z => z i j) he).trans hy⟩
    | inr i =>
      obtain ⟨y,hy⟩ := hr i j u
      obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x,hx⟩,(congrArg (fun z => z i j) he).trans hy⟩

theorem splitFull_map_iff (K : Subgroup (OrbitProfileProductGroup m U)) :
    SplitFull m U (K.map (equiv m U).toMonoidHom) ↔ OrbitProfileProductFull m U K := by
  unfold SplitFull
  rw [Subgroup.map_map,Subgroup.map_map]
  exact (full_iff_projection_full m U K).symm

/-- Both classes are full in their individual original coordinates. Neither
projection to an entire class product is required to be onto. -/
def familyEquiv (P : Subgroup (OrbitProfileProductGroup m U) → Prop) :
    {K : Subgroup (OrbitProfileProductGroup m U) // OrbitProfileProductFull m U K ∧ P K} ≃
      {L : Subgroup (Left m U × Right m U) // SplitFull m U L ∧
        P (L.comap (equiv m U).toMonoidHom)} where
  toFun K := ⟨K.1.map (equiv m U).toMonoidHom,
    (splitFull_map_iff m U K.1).mpr K.2.1,by
      rw [Subgroup.comap_map_eq_self_of_injective
        (f := (equiv m U).toMonoidHom) (equiv m U).injective]
      exact K.2.2⟩
  invFun L := ⟨L.1.comap (equiv m U).toMonoidHom,by
    apply (splitFull_map_iff m U _).mp
    rw [Subgroup.map_comap_eq_self_of_surjective
      (f := (equiv m U).toMonoidHom) (equiv m U).surjective]
    exact L.2.1,L.2.2⟩
  left_inv K := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective (equiv m U).injective K.1
  right_inv L := by
    apply Subtype.ext
    exact Subgroup.map_comap_eq_self_of_surjective (equiv m U).surjective L.1

theorem familyEquiv_reconstruct (P : Subgroup (OrbitProfileProductGroup m U) → Prop)
    (K : {K : Subgroup (OrbitProfileProductGroup m U) // OrbitProfileProductFull m U K ∧ P K}) :
    (familyEquiv m U P K).1.comap (equiv m U).toMonoidHom = K.1 :=
  Subgroup.comap_map_eq_self_of_injective (equiv m U).injective K.1

end SymmetricSubgroupAsymptotics.OrbitProfileProductSum
