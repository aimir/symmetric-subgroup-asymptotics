import SymmetricSubgroupAsymptotics.FiniteNormalJoinCoverRegistry
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistryTransport

/-!
# Existing normal-join word fields with an original-row conjugacy cover

The six fields below are the existing generated normal-certificate fields.
Only the conjugacy input changes: an actual original-group row/conjugator
cover supplies coverage, without a global class invariant or centralizer
counts. Representative identification is explicit when an existing tuple is
used. The compatibility adapter does not erase dependencies of an old proof;
new literal chains must supply their checked cover and word fields directly.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace FiniteConjugacyCover

/-- Transport the actual rows and their conjugators through a group
equivalence. This is equality of group models, not an overgroup argument. -/
def mapEquiv {G H : Type*} [Group G] [Group H] {n c : ℕ}
    {rows : Fin n → G} (C : FiniteConjugacyCover rows c) (e : G ≃* H) :
    FiniteConjugacyCover (fun i => e (rows i)) c where
  complete y := by
    obtain ⟨i, hi⟩ := C.complete (e.symm y)
    refine ⟨i, ?_⟩
    change e (rows i) = y
    rw [hi]
    exact e.apply_symm_apply y
  representative := C.representative
  label := C.label
  conjugator := C.conjugator
  conjugates i := by
    simpa only [map_mul] using congrArg e (C.conjugates i)

end FiniteConjugacyCover

/-- Proof-carrying original normal-state data with precisely the same word
and transition fields as `FiniteNormalJoinWordRegistryData`. -/
structure FiniteNormalJoinCoverWordRegistryData
    {G I ι κ : Type*} [Group G] {n c : ℕ} {rows : Fin n → G}
    (C : FiniteConjugacyCover rows c)
    (ambient : ι → G) (stateGenerators : I → κ → G) where
  ambient_full : Subgroup.closure (Set.range ambient) = ⊤
  normality : ∀ i,
    FiniteNormalityWordCertificate ambient (stateGenerators i)
  bottom : I
  bottom_eq : Subgroup.closure (Set.range (stateGenerators bottom)) = ⊥
  child : I → Fin c → I
  transition : ∀ i j,
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (rows (C.representative j))
      (stateGenerators (child i j))

namespace FiniteNormalJoinCoverWordRegistryData

/-- Install the original generated states and the exact checked joins. -/
def toRegistry
    {G I ι κ : Type*} [Group G] {n c : ℕ} {rows : Fin n → G}
    {C : FiniteConjugacyCover rows c} {ambient : ι → G}
    {stateGenerators : I → κ → G}
    (D : FiniteNormalJoinCoverWordRegistryData C ambient stateGenerators) :
    FiniteNormalJoinCoverRegistry C
      (fun i => Subgroup.closure (Set.range (stateGenerators i))) where
  normal i := (D.normality i).normal D.ambient_full
  bottom := D.bottom
  bottom_eq := D.bottom_eq
  child := D.child
  child_eq i j := by
    letI : (Subgroup.closure
        (Set.range (stateGenerators (D.child i j)))).Normal :=
      (D.normality (D.child i j)).normal D.ambient_full
    exact (D.transition i j).join_eq.symm

/-- Completeness is proved from the actual row cover and the existing words;
there is no normal-list completeness input. -/
theorem complete
    {G I ι κ : Type*} [Group G] {n c : ℕ} {rows : Fin n → G}
    {C : FiniteConjugacyCover rows c} {ambient : ι → G}
    {stateGenerators : I → κ → G}
    (D : FiniteNormalJoinCoverWordRegistryData C ambient stateGenerators)
    (N : Subgroup G) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  D.toRegistry.complete N

/-- Bind an existing representative tuple to the actual cover, then reuse
all six generated fields without changing a state or a transition. -/
def ofFields
    {G I ι κ : Type*} [Group G] {n c : ℕ} {rows : Fin n → G}
    (C : FiniteConjugacyCover rows c)
    (representative : Fin c → G)
    (representative_eq : ∀ j, rows (C.representative j) = representative j)
    (ambient : ι → G) (stateGenerators : I → κ → G)
    (ambient_full : Subgroup.closure (Set.range ambient) = ⊤)
    (normality : ∀ i, FiniteNormalityWordCertificate ambient (stateGenerators i))
    (bottom : I)
    (bottom_eq : Subgroup.closure (Set.range (stateGenerators bottom)) = ⊥)
    (child : I → Fin c → I)
    (transition : ∀ i j,
      FiniteNormalJoinTransitionCertificate
        (stateGenerators i) (representative j) (stateGenerators (child i j))) :
    FiniteNormalJoinCoverWordRegistryData C ambient stateGenerators where
  ambient_full := ambient_full
  normality := normality
  bottom := bottom
  bottom_eq := bottom_eq
  child := child
  transition i j := by
    rw [representative_eq j]
    exact transition i j

/-- Compatibility with an existing cardinal-cover word object. This merely
reuses its fields; it does not remove any axioms in that object's proof.
A new standard-axiom literal route should use `ofFields` directly. -/
def ofCardinalData
    {G I ι κ : Type*} [Group G] [Finite G] {n c : ℕ} {rows : Fin n → G}
    {representative : Fin c → G}
    {oldCover : FiniteConjugacyCardinalCover representative}
    {ambient : ι → G} {stateGenerators : I → κ → G}
    (C : FiniteConjugacyCover rows c)
    (representative_eq : ∀ j, rows (C.representative j) = representative j)
    (D : FiniteNormalJoinWordRegistryData oldCover ambient stateGenerators) :
    FiniteNormalJoinCoverWordRegistryData C ambient stateGenerators :=
  ofFields C representative representative_eq ambient stateGenerators
    D.ambient_full D.normality D.bottom D.bottom_eq D.child D.transition

/-- Carry the same word equations and states through an actual group
identification. The cover transports its original-group conjugators too. -/
def mapEquiv
    {G H I ι κ : Type*} [Group G] [Group H] {n c : ℕ} {rows : Fin n → G}
    {C : FiniteConjugacyCover rows c} {ambient : ι → G}
    {stateGenerators : I → κ → G}
    (D : FiniteNormalJoinCoverWordRegistryData C ambient stateGenerators)
    (e : G ≃* H) :
    FiniteNormalJoinCoverWordRegistryData (C.mapEquiv e)
      (fun i => e (ambient i)) (fun s j => e (stateGenerators s j)) where
  ambient_full := by
    rw [closure_range_map_equiv, D.ambient_full]
    exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
  normality i := (D.normality i).mapEquiv e
  bottom := D.bottom
  bottom_eq := by
    rw [closure_range_map_equiv, D.bottom_eq, map_bot_equiv]
  child := D.child
  transition i j := (D.transition i j).mapEquiv e

/-- The unchanged two-transition reachability witness yields two ambient
normal generators in the original group. -/
theorem normal_generating_pair
    {G I ι κ : Type} [Group G] {n c : ℕ} {rows : Fin n → G}
    {C : FiniteConjugacyCover rows c} {ambient : ι → G}
    {stateGenerators : I → κ → G}
    (D : FiniteNormalJoinCoverWordRegistryData C ambient stateGenerators)
    (hreach : ∀ i, ∃ a b, D.child (D.child D.bottom a) b = i)
    (N : Subgroup G) [N.Normal] :
    ∃ x : Fin 2 → G, Subgroup.normalClosure (Set.range x) = N :=
  D.toRegistry.normal_generating_pair hreach N

/-- Every original normal quotient has the same two-generator socle bound. -/
theorem quotientSocle_two
    {G I ι κ : Type} [Group G] {n c : ℕ} {rows : Fin n → G}
    {C : FiniteConjugacyCover rows c} {ambient : ι → G}
    {stateGenerators : I → κ → G}
    (D : FiniteNormalJoinCoverWordRegistryData C ambient stateGenerators)
    (hreach : ∀ i, ∃ a b, D.child (D.child D.bottom a) b = i)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 :=
  D.toRegistry.quotientSocle_two hreach N

end FiniteNormalJoinCoverWordRegistryData
end SymmetricSubgroupAsymptotics

end
