import SymmetricSubgroupAsymptotics.MarkedC4PublishedOrdinaryNilpotentGeneration
import SymmetricSubgroupAsymptotics.MarkedC4SocleSurjectiveImage
import SymmetricSubgroupAsymptotics.SolubleSubdirectSocleIntersection

/-!
RDT Lemma 8.5 for the literal upper socle height. The intersection of the
factor-socle inverse images is proved equal to the original socle by the
integral conjugation-module argument. Quotienting by these actual socles
therefore retains a subdirect embedding, and induction proves the bound.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration

/-- Surjective homomorphisms cannot increase the literal upper socle
height. Neither finiteness nor solubility is needed for this direction. -/
theorem height_of_surjective {n : ℕ} {G H : Type} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (h : Height n G) :
    Height n H := by
  induction n generalizing G H with
  | zero =>
      letI : Subsingleton G := h
      exact hf.subsingleton
  | succ n ih =>
      let hs : finiteGroupSocle G ≤ (finiteGroupSocle H).comap f :=
        SocleSurjectiveImage.socle_le_comap f hf
      let q : (G ⧸ finiteGroupSocle G) →* (H ⧸ finiteGroupSocle H) :=
        QuotientGroup.map (finiteGroupSocle G) (finiteGroupSocle H) f hs
      have hq : Function.Surjective q :=
        QuotientGroup.map_surjective_of_surjective
          (finiteGroupSocle G) (finiteGroupSocle H) f
          ((QuotientGroup.mk'_surjective (finiteGroupSocle H)).comp hf) hs
      exact ih q hq h

/-- Literal upper socle height transports along an actual group
isomorphism, including between different presentations of a quotient. -/
theorem height_equiv {n : ℕ} {G H : Type} [Group G] [Group H]
    (e : G ≃* H) : Height n G ↔ Height n H :=
  ⟨height_of_surjective e.toMonoidHom e.surjective,
    height_of_surjective e.symm.toMonoidHom e.symm.surjective⟩

/-- A quotient has no greater literal upper socle height than its source. -/
theorem height_quotient {n : ℕ} {G : Type} [Group G]
    (N : Subgroup G) [N.Normal] (h : Height n G) : Height n (G ⧸ N) :=
  height_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) h

set_option maxHeartbeats 1000000 in
/-- If a normal subgroup lies in the first literal socle layer, any
height bound on its quotient gives one further layer for the source. -/
theorem height_succ_of_quotient {n : ℕ} {G : Type} [Group G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ finiteGroupSocle G)
    (h : Height n (G ⧸ N)) : Height (n + 1) G := by
  change Height n (G ⧸ finiteGroupSocle G)
  let hs : N ≤ (finiteGroupSocle G).comap (MonoidHom.id G) := by
    simpa only [Subgroup.comap_id] using hN
  let q : (G ⧸ N) →* (G ⧸ finiteGroupSocle G) :=
    QuotientGroup.map N (finiteGroupSocle G) (MonoidHom.id G) hs
  have hq : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective N (finiteGroupSocle G)
      (MonoidHom.id G) (QuotientGroup.mk'_surjective (finiteGroupSocle G)) hs
  exact height_of_surjective (n := n) q hq h

private def socleQuotientProjection {I : Type} (F : I → Type) [∀ i, Group (F i)]
    {G : Type} [Group G] (f : G →* ∀ i, F i)
    (hs : ∀ i, Function.Surjective (fun g => f g i)) (i : I) :
    (G ⧸ finiteGroupSocle G) →* (F i ⧸ finiteGroupSocle (F i)) :=
  QuotientGroup.map (finiteGroupSocle G) (finiteGroupSocle (F i))
    (SolubleSubdirectSocleIntersection.coordinate F f i)
    (SocleSurjectiveImage.socle_le_comap
      (SolubleSubdirectSocleIntersection.coordinate F f i) (hs i))

private def socleQuotientMap {I : Type} (F : I → Type) [∀ i, Group (F i)]
    {G : Type} [Group G] (f : G →* ∀ i, F i)
    (hs : ∀ i, Function.Surjective (fun g => f g i)) :
    (G ⧸ finiteGroupSocle G) →* ∀ i, F i ⧸ finiteGroupSocle (F i) :=
  Pi.monoidHom (socleQuotientProjection F f hs)

private theorem socleQuotientProjection_surjective {I : Type}
    (F : I → Type) [∀ i, Group (F i)]
    {G : Type} [Group G] (f : G →* ∀ i, F i)
    (hs : ∀ i, Function.Surjective (fun g => f g i)) (i : I) :
    Function.Surjective (socleQuotientProjection F f hs i) :=
  QuotientGroup.map_surjective_of_surjective (finiteGroupSocle G)
    (finiteGroupSocle (F i)) (SolubleSubdirectSocleIntersection.coordinate F f i)
    ((QuotientGroup.mk'_surjective (finiteGroupSocle (F i))).comp (hs i))
    (SocleSurjectiveImage.socle_le_comap
      (SolubleSubdirectSocleIntersection.coordinate F f i) (hs i))

private theorem socleQuotientMap_injective {I : Type} [Finite I]
    (F : I → Type) [∀ i, Group (F i)] [∀ i, Finite (F i)]
    [∀ i, IsSolvable (F i)]
    {G : Type} [Group G] (f : G →* ∀ i, F i) (hf : Function.Injective f)
    (hs : ∀ i, Function.Surjective (fun g => f g i)) :
    Function.Injective (socleQuotientMap F f hs) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro q hq
  apply Subgroup.mem_bot.mpr
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (finiteGroupSocle G) q
  apply (QuotientGroup.eq_one_iff g).mpr
  rw [← SolubleSubdirectSocleIntersection.preimage_eq_socle F f hf hs]
  apply (SolubleSubdirectSocleIntersection.mem_preimage F f g).mpr
  intro i
  have hi := congrFun (MonoidHom.mem_ker.mp hq) i
  change QuotientGroup.mk' (finiteGroupSocle (F i))
    (SolubleSubdirectSocleIntersection.coordinate F f i g) = 1 at hi
  exact (QuotientGroup.eq_one_iff _).mp hi

private theorem height_subdirect (L : ℕ) :
    ∀ (I : Type) [Fintype I] [Nonempty I]
      (F : I → Type) [∀ i, Group (F i)] [∀ i, Finite (F i)] [∀ i, IsSolvable (F i)]
      (G : Type) [Group G] [Finite G] [IsSolvable G]
      (f : G →* ∀ i, F i), Function.Injective f →
      (∀ i, Function.Surjective (fun g => f g i)) →
      (∀ i, Height L (F i)) → Height L G := by
  induction L with
  | zero =>
      intro I _ _ F _ _ _ G _ _ _ f hf _ hF
      change Subsingleton G
      constructor
      intro a b
      apply hf
      funext i
      letI : Subsingleton (F i) := hF i
      exact Subsingleton.elim _ _
  | succ L ih =>
      intro I _ _ F _ _ _ G _ _ _ f hf hs hF
      exact ih I (fun i => F i ⧸ finiteGroupSocle (F i))
        (G ⧸ finiteGroupSocle G) (socleQuotientMap F f hs)
        (socleQuotientMap_injective F f hf hs)
        (socleQuotientProjection_surjective F f hs) hF

/-- The exact published soluble subdirect-height input is a theorem for
successive quotients by the literal finite-group socle. -/
theorem publishedSolubleSubdirectHeight : PublishedSolubleSubdirectHeight := by
  intro I _ _ F _ _ _ G _ _ _ f hf hs L hF
  exact height_subdirect L I F G f hf hs hF

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
