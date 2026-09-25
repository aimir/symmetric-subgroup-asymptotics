import SymmetricSubgroupAsymptotics.BinaryFamilies
import SymmetricSubgroupAsymptotics.BinaryAbelianization

/-!
# Shared-source graph moments

A tuple of quotient maps is encoded over one original source subgroup.
The pullback graph retains that subgroup and every coordinate map exactly.
A faithful action on disjoint original blocks turns this into an injection
into actual permutation subgroups, without independently summing sources.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G A B : Type*} [Group G] [Group A] [Group B]

/-- All quotient maps in a tuple have the same actual source subgroup. -/
abbrev JointSourceMaps (G B : Type*) [Group G] [Group B] (q : ℕ) :=
  Σ J : Subgroup G, Fin q → (J →* B)

/-- Literal pullback graph in the cover product and original ambient group. -/
def jointSourceGraph (π : A →* B) {q : ℕ} (data : JointSourceMaps G B q) :
    Subgroup ((Fin q → A) × G) where
  carrier := {v | ∃ j : data.1, v.2 = j.1 ∧ ∀ i, π (v.1 i) = data.2 i j}
  one_mem' := ⟨1, rfl, by intro i; simp⟩
  mul_mem' := by
    rintro x y ⟨j,hj,hf⟩ ⟨k,hk,hg⟩
    refine ⟨j*k, ?_, ?_⟩
    · change x.2 * y.2 = j.1 * k.1
      rw [hj,hk]
    · intro i
      change π (x.1 i * y.1 i) = data.2 i (j*k)
      rw [map_mul,map_mul,hf,hg]
  inv_mem' := by
    rintro x ⟨j,hj,hf⟩
    refine ⟨j⁻¹, ?_, ?_⟩
    · change x.2⁻¹ = j.1⁻¹
      rw [hj]
    · intro i
      change π (x.1 i)⁻¹ = data.2 i (j⁻¹)
      rw [map_inv,map_inv,hf]

/-- Every original source element has a nonempty simultaneous graph fibre. -/
theorem jointSourceGraph_lift (π : A →* B) (hπ : Function.Surjective π)
    {q : ℕ} (data : JointSourceMaps G B q) (j : data.1) :
    ∃ a : Fin q → A, (a,j.1) ∈ jointSourceGraph π data := by
  choose a ha using fun i => hπ (data.2 i j)
  exact ⟨a,j,rfl,ha⟩

/-- Projection recovers the literal source subgroup, not just its isomorphism type. -/
theorem jointSourceGraph_source (π : A →* B) (hπ : Function.Surjective π)
    {q : ℕ} (data : JointSourceMaps G B q) :
    (jointSourceGraph π data).map (MonoidHom.snd _ _) = data.1 := by
  ext g
  constructor
  · rintro ⟨v,⟨j,hj,_⟩,hv⟩
    change v.2 = g at hv
    rw [← hv,hj]
    exact j.2
  · intro hg
    obtain ⟨a,ha⟩ := jointSourceGraph_lift π hπ data ⟨g,hg⟩
    exact ⟨(a,g),ha,rfl⟩

/-- All maps, including correlations among them, are recovered from one graph. -/
theorem jointSourceGraph_injective (π : A →* B) (hπ : Function.Surjective π)
    (q : ℕ) : Function.Injective (jointSourceGraph (G := G) π (q := q)) := by
  rintro ⟨J,f⟩ ⟨K,g⟩ h
  have hJK : J = K := by
    calc
      J = (jointSourceGraph π ⟨J,f⟩).map (MonoidHom.snd _ _) :=
        (jointSourceGraph_source π hπ ⟨J,f⟩).symm
      _ = (jointSourceGraph π ⟨K,g⟩).map (MonoidHom.snd _ _) := by rw [h]
      _ = K := jointSourceGraph_source π hπ ⟨K,g⟩
  subst K
  have hfg : f = g := by
    funext i
    apply MonoidHom.ext
    intro j
    obtain ⟨a,ha⟩ := jointSourceGraph_lift π hπ ⟨J,f⟩ j
    have hb : (a,j.1) ∈ jointSourceGraph π ⟨J,g⟩ := h ▸ ha
    obtain ⟨k,hk,hg⟩ := hb
    have hkj : k = j := Subtype.ext hk.symm
    subst k
    obtain ⟨k,hk,hf⟩ := ha
    have hkj : k = j := Subtype.ext hk.symm
    subst k
    exact (hf i).symm.trans (hg i)
  subst g
  rfl


/-- The original cover coordinate, before relabelling. -/
def jointSourceCoverProjection (q : ℕ) (i : Fin q) : ((Fin q → A) × G) →* A where
  toFun v := v.1 i
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A graph fibre remembers every literal quotient-map value. -/
theorem jointSourceGraph_fibre_iff (π : A →* B) {q : ℕ}
    (data : JointSourceMaps G B q) (a : Fin q → A) (j : data.1) :
    (a,j.1) ∈ jointSourceGraph π data ↔ ∀ i, π (a i) = data.2 i j := by
  constructor
  · rintro ⟨k,hk,hf⟩
    have hkj : k = j := Subtype.ext hk.symm
    subst k
    exact hf
  · exact fun hf => ⟨j,rfl,hf⟩

/-- The original cover projection is the complete pullback of its map range. -/
theorem jointSourceGraph_marginal (π : A →* B) (hπ : Function.Surjective π)
    {q : ℕ} (data : JointSourceMaps G B q) (i : Fin q) :
    (jointSourceGraph π data).map (jointSourceCoverProjection q i) =
      (data.2 i).range.comap π := by
  classical
  ext a
  constructor
  · rintro ⟨v,⟨j,hj,hf⟩,ha⟩
    change v.1 i = a at ha
    exact ⟨j,by rw [← ha]; exact (hf i).symm⟩
  · rintro ⟨j,hj⟩
    choose a₀ ha₀ using fun l => hπ (data.2 l j)
    refine ⟨(Function.update a₀ i a,j.1),⟨j,rfl,?_⟩,?_⟩
    · intro l
      by_cases hl : l = i
      · subst l
        simpa using hj.symm
      · simpa [Function.update,hl] using ha₀ l
    · simp [jointSourceCoverProjection]

/-- An onto map gives a full original cover projection. Thus the encoding
really is subdirect on each retained cover and its actual source. -/
theorem jointSourceGraph_full_cover (π : A →* B) (hπ : Function.Surjective π)
    {q : ℕ} (data : JointSourceMaps G B q) (i : Fin q)
    (hi : Function.Surjective (data.2 i)) :
    (jointSourceGraph π data).map (jointSourceCoverProjection q i) = ⊤ := by
  rw [jointSourceGraph_marginal π hπ,MonoidHom.range_eq_top.mpr hi]
  rfl


/-- The faithful disjoint-block action retains the source and each cover copy. -/
def jointDisjointAction {X Z : Type*} (ρ : A →* Equiv.Perm X) (q : ℕ) :
    ((Fin q → A) × Equiv.Perm Z) →* Equiv.Perm (Z ⊕ (Fin q × X)) where
  toFun v :=
    { toFun := fun z => match z with
        | .inl z => .inl (v.2 z)
        | .inr (i,x) => .inr (i,ρ (v.1 i) x)
      invFun := fun z => match z with
        | .inl z => .inl (v.2.symm z)
        | .inr (i,x) => .inr (i,(ρ (v.1 i)).symm x)
      left_inv := by rintro (z | ⟨i,x⟩) <;> simp
      right_inv := by rintro (z | ⟨i,x⟩) <;> simp }
  map_one' := by
    apply Equiv.ext
    rintro (z | ⟨i,x⟩) <;> simp
  map_mul' u v := by
    apply Equiv.ext
    rintro (z | ⟨i,x⟩) <;> simp

theorem jointDisjointAction_injective {X Z : Type*} (ρ : A →* Equiv.Perm X)
    (hρ : Function.Injective ρ) (q : ℕ) :
    Function.Injective (jointDisjointAction (Z := Z) ρ q) := by
  intro u v h
  apply Prod.ext
  · funext i
    apply hρ
    apply Equiv.ext
    intro x
    have he := Equiv.congr_fun h (Sum.inr (i,x))
    exact congrArg Prod.snd (Sum.inr.inj he)
  · apply Equiv.ext
    intro z
    exact Sum.inl.inj (Equiv.congr_fun h (Sum.inl z))

/-- A fixed label chart for the original disjoint source and cover blocks. -/
def jointDisjointLabels (b s q : ℕ) :
    (Fin b ⊕ (Fin q × Fin s)) ≃ Fin (b + q*s) :=
  Fintype.equivOfCardEq (by simp)

/-- Literal faithful action in the original total degree. -/
def jointDisjointFiniteAction {s : ℕ} (ρ : A →* Equiv.Perm (Fin s))
    (b q : ℕ) : ((Fin q → A) × Equiv.Perm (Fin b)) →*
      Equiv.Perm (Fin (b+q*s)) :=
  (jointDisjointLabels b s q).permCongrHom.toMonoidHom.comp (jointDisjointAction ρ q)

theorem jointDisjointFiniteAction_injective {s : ℕ} (ρ : A →* Equiv.Perm (Fin s))
    (hρ : Function.Injective ρ) (b q : ℕ) :
    Function.Injective (jointDisjointFiniteAction ρ b q) :=
  (jointDisjointLabels b s q).permCongrHom.injective.comp (jointDisjointAction_injective ρ hρ q)

/-- The exact shared-source graph injection into labelled permutation subgroups. -/
def jointSourcePermutationGraph {s : ℕ} (ρ : A →* Equiv.Perm (Fin s))
    (π : A →* B) (b q : ℕ) :
    JointSourceMaps (Equiv.Perm (Fin b)) B q → Subgroup (Equiv.Perm (Fin (b+q*s))) :=
  fun data => (jointSourceGraph π data).map (jointDisjointFiniteAction ρ b q)

theorem jointSourcePermutationGraph_injective {s : ℕ} (ρ : A →* Equiv.Perm (Fin s))
    (hρ : Function.Injective ρ) (π : A →* B) (hπ : Function.Surjective π)
    (b q : ℕ) : Function.Injective (jointSourcePermutationGraph ρ π b q) :=
  (Subgroup.map_injective (jointDisjointFiniteAction_injective ρ hρ b q)).comp
    (jointSourceGraph_injective π hπ q)

/-- A graph moment with the same original source in every factor. -/
theorem jointSourceHom_moment_le [Finite B] {s : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (π : A →* B) (hπ : Function.Surjective π) (b q : ℕ) :
    ∑ J : Subgroup (Equiv.Perm (Fin b)), Nat.card (J →* B) ^ q ≤ subgroupCount (b+q*s) := by
  classical
  letI : Fintype (Subgroup (Equiv.Perm (Fin b))) := Fintype.ofFinite _
  letI (J : Subgroup (Equiv.Perm (Fin b))) : Finite (J →* B) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hcard := Nat.card_le_card_of_injective _ (jointSourcePermutationGraph_injective ρ hρ π hπ b q)
  change Nat.card (JointSourceMaps (Equiv.Perm (Fin b)) B q) ≤ subgroupCount (b+q*s) at hcard
  rw [JointSourceMaps,Nat.card_sigma] at hcard
  simpa only [Nat.card_fun,Nat.card_fin] using hcard


/-- Surjective quotient maps are retained as actual homomorphisms. -/
abbrev GroupEpimorphism (J B : Type*) [Group J] [Group B] :=
  {f : J →* B // Function.Surjective f}

/-- Epimorphisms and characters are paired over the same source and repeated
jointly; the source is not chosen independently for different factors. -/
abbrev JointMarkedSourceMaps (G B M : Type*) [Group G] [Group B] [Group M] (q : ℕ) :=
  Σ J : Subgroup G, Fin q → (GroupEpimorphism J B × (J →* M))

def jointMarkedSourceToMaps {M : Type*} [Group M] (q : ℕ) :
    JointMarkedSourceMaps G B M q → JointSourceMaps G (B × M) q :=
  Sigma.map id (fun _ f i => (f i).1.1.prod (f i).2)

theorem jointMarkedSourceToMaps_injective {M : Type*} [Group M] (q : ℕ) :
    Function.Injective (jointMarkedSourceToMaps (G := G) (B := B) (M := M) q) := by
  apply Function.injective_id.sigma_map
  intro J f g h
  funext i
  apply Prod.ext
  · apply Subtype.ext
    apply MonoidHom.ext
    intro j
    exact congrArg Prod.fst (DFunLike.congr_fun (congrFun h i) j)
  · apply MonoidHom.ext
    intro j
    exact congrArg Prod.snd (DFunLike.congr_fun (congrFun h i) j)

/-- The cover and marker act on separate literal blocks. -/
def jointAuxiliaryAction {M : Type*} [Group M] {s t : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (μ : M →* Equiv.Perm (Fin t)) :
    A × M →* Equiv.Perm (Fin (s+t)) :=
  (Fintype.equivOfCardEq (by simp) : (Fin s ⊕ Fin t) ≃ Fin (s+t)).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin s) (Fin t)).comp (ρ.prodMap μ))

theorem jointAuxiliaryAction_injective {M : Type*} [Group M] {s t : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (μ : M →* Equiv.Perm (Fin t)) (hμ : Function.Injective μ) :
    Function.Injective (jointAuxiliaryAction ρ μ) := by
  intro u v h
  have h1 := (Fintype.equivOfCardEq (by simp) :
    (Fin s ⊕ Fin t) ≃ Fin (s+t)).permCongrHom.injective h
  have h2 := Equiv.Perm.sumCongrHom_injective h1
  exact Prod.ext (hρ (congrArg Prod.fst h2)) (hμ (congrArg Prod.snd h2))

/-- A literal marked graph in the original total permutation degree. -/
def jointMarkedPermutationGraph {M : Type*} [Group M] {s t : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (μ : M →* Equiv.Perm (Fin t))
    (π : A →* B) (b q : ℕ) :
    JointMarkedSourceMaps (Equiv.Perm (Fin b)) B M q →
      Subgroup (Equiv.Perm (Fin (b+q*(s+t)))) :=
  jointSourcePermutationGraph (jointAuxiliaryAction ρ μ) (π.prodMap (MonoidHom.id M)) b q
    ∘ jointMarkedSourceToMaps q

theorem jointMarkedPermutationGraph_injective {M : Type*} [Group M] {s t : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (μ : M →* Equiv.Perm (Fin t)) (hμ : Function.Injective μ)
    (π : A →* B) (hπ : Function.Surjective π) (b q : ℕ) :
    Function.Injective (jointMarkedPermutationGraph ρ μ π b q) := by
  apply (jointSourcePermutationGraph_injective (jointAuxiliaryAction ρ μ)
    (jointAuxiliaryAction_injective ρ hρ μ hμ) (π.prodMap (MonoidHom.id M)) ?_ b q).comp
    (jointMarkedSourceToMaps_injective q)
  rintro ⟨x,y⟩
  obtain ⟨a,ha⟩ := hπ x
  exact ⟨(a,y),Prod.ext ha rfl⟩

/-- The full mixed moment is controlled in one disjoint permutation action. -/
theorem jointSourceMarked_moment_le {M : Type*} [Group M] {s t : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (μ : M →* Equiv.Perm (Fin t)) (hμ : Function.Injective μ)
    (π : A →* B) (hπ : Function.Surjective π) (b q : ℕ) :
    ∑ J : Subgroup (Equiv.Perm (Fin b)),
      (Nat.card (GroupEpimorphism J B) * Nat.card (J →* M)) ^ q
      ≤ subgroupCount (b+q*(s+t)) := by
  classical
  letI : Finite A := Finite.of_injective ρ hρ
  letI : Finite B := Finite.of_surjective π hπ
  letI : Finite M := Finite.of_injective μ hμ
  letI : Fintype (Subgroup (Equiv.Perm (Fin b))) := Fintype.ofFinite _
  letI (J : Subgroup (Equiv.Perm (Fin b))) : Finite (J →* B) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI (J : Subgroup (Equiv.Perm (Fin b))) : Finite (J →* M) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hcard := Nat.card_le_card_of_injective _
    (jointMarkedPermutationGraph_injective ρ hρ μ hμ π hπ b q)
  change Nat.card (JointMarkedSourceMaps (Equiv.Perm (Fin b)) B M q)
    ≤ subgroupCount (b+q*(s+t)) at hcard
  rw [JointMarkedSourceMaps,Nat.card_sigma] at hcard
  simpa only [Nat.card_fun,Nat.card_fin,Nat.card_prod] using hcard

/-- c independent binary characters use c literal two-point blocks. -/
def binaryMarkerAction (c : ℕ) :
    Multiplicative (Fin c → ZMod 2) →* Equiv.Perm (Fin c × ZMod 2) where
  toFun a :=
    { toFun := fun x => (x.1,x.2+a.toAdd x.1)
      invFun := fun x => (x.1,x.2-a.toAdd x.1)
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  map_one' := by ext x <;> simp
  map_mul' a b := by ext x <;> simp [add_comm,add_left_comm]

theorem binaryMarkerAction_injective (c : ℕ) : Function.Injective (binaryMarkerAction c) := by
  intro a b h
  apply Multiplicative.toAdd.injective
  funext i
  have hi := congrArg Prod.snd (Equiv.congr_fun h (i,0))
  simpa [binaryMarkerAction] using hi

def binaryMarkerFiniteAction (c : ℕ) :
    Multiplicative (Fin c → ZMod 2) →* Equiv.Perm (Fin (2*c)) :=
  (Fintype.equivOfCardEq (by simp [Nat.mul_comm]) :
    (Fin c × ZMod 2) ≃ Fin (2*c)).permCongrHom.toMonoidHom.comp (binaryMarkerAction c)

theorem binaryMarkerFiniteAction_injective (c : ℕ) :
    Function.Injective (binaryMarkerFiniteAction c) :=
  (Fintype.equivOfCardEq (by simp [Nat.mul_comm]) :
    (Fin c × ZMod 2) ≃ Fin (2*c)).permCongrHom.injective.comp (binaryMarkerAction_injective c)

/-- Joint epimorphism/character moments on the same actual source. The
binary marker degree is linear in the number of retained characters. -/
theorem jointSourceBinaryMarked_moment_le {s : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (π : A →* B) (hπ : Function.Surjective π) (b c q : ℕ) :
    ∑ J : Subgroup (Equiv.Perm (Fin b)),
      (Nat.card (GroupEpimorphism J B) *
        Nat.card (J →* Multiplicative (Fin c → ZMod 2))) ^ q
      ≤ subgroupCount (b+q*(s+2*c)) :=
  jointSourceMarked_moment_le ρ hρ (binaryMarkerFiniteAction c)
    (binaryMarkerFiniteAction_injective c) π hπ b q


/-- The manuscript's exact numerical moment, with the binary rank of the
whole original source. The same J remains inside every power. -/
theorem jointSourceEpimorphism_binaryRank_moment_le {s : ℕ}
    (ρ : A →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (π : A →* B) (hπ : Function.Surjective π) (b c q : ℕ) :
    ∑ J : Subgroup (Equiv.Perm (Fin b)),
      (Nat.card (GroupEpimorphism J B) * 2^(c * binaryCharacterRank J)) ^ q
      ≤ subgroupCount (b+q*(s+2*c)) := by
  simpa only [binaryAbelianizationGroupHom_card, Module.finrank_pi,
    Fintype.card_fin, Nat.mul_comm] using
    jointSourceBinaryMarked_moment_le ρ hρ π hπ b c q

end SymmetricSubgroupAsymptotics
