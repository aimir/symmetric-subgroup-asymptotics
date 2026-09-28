import SymmetricSubgroupAsymptotics.FusionGoursatCount

/-!
# Complete quotient moments over one literal source

The complete quotient count retains every literal normal subgroup of the
target.  A tuple of such quotient maps is encoded over one common source
subgroup by a simultaneous pullback graph.  Projection recovers the source
and every coordinate graph, so the encoding is injective even when different
coordinates use different normal axes or isomorphic quotient groups.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G R : Type*} [Group G] [Group R]

/-- One literal normal axis of `R` and one onto map from the same source. -/
abbrev CompleteQuotientMap (J : Type*) [Group J] (R : Type*) [Group R] :=
  Σ N : {N : Subgroup R // N.Normal}, GroupEpimorphism J (R ⧸ N.1)

/-- A tuple of complete quotient maps sharing one actual source subgroup. -/
abbrev JointCompleteQuotientData (G R : Type*) [Group G] [Group R] (q : ℕ) :=
  Σ J : Subgroup G, Fin q → CompleteQuotientMap J R

/-- The explicit sum over all literal normal axes. -/
def completeQuotientCount [Finite R] (J : Subgroup G) : ℕ :=
  ∑ N : {N : Subgroup R // N.Normal},
    Nat.card (GroupEpimorphism J (R ⧸ N.1))

theorem completeQuotientMap_card [Finite G] [Finite R] (J : Subgroup G) :
    Nat.card (CompleteQuotientMap J R) = completeQuotientCount (R := R) J := by
  rw [CompleteQuotientMap, Nat.card_sigma]
  rfl

/-- Simultaneous quotient graph with every normal axis retained. -/
def jointCompleteQuotientGraph {q : ℕ} (data : JointCompleteQuotientData G R q) :
    Subgroup ((Fin q → R) × G) where
  carrier := {x | ∃ j : data.1, (j : G) = x.2 ∧ ∀ i,
    QuotientGroup.mk' (data.2 i).1.1 (x.1 i) = (data.2 i).2.1 j}
  one_mem' := ⟨1, rfl, by intro i; simp⟩
  mul_mem' := by
    rintro x y ⟨j, hj, hx⟩ ⟨k, hk, hy⟩
    refine ⟨j * k, ?_, ?_⟩
    · change (j : G) * (k : G) = x.2 * y.2
      rw [hj, hk]
    · intro i
      change QuotientGroup.mk' (data.2 i).1.1 (x.1 i * y.1 i) =
        (data.2 i).2.1 (j * k)
      rw [map_mul, map_mul, hx i, hy i]
  inv_mem' := by
    rintro x ⟨j, hj, hx⟩
    refine ⟨j⁻¹, ?_, ?_⟩
    · change (j : G)⁻¹ = x.2⁻¹
      rw [hj]
    · intro i
      change QuotientGroup.mk' (data.2 i).1.1 (x.1 i)⁻¹ =
        (data.2 i).2.1 j⁻¹
      rw [map_inv, map_inv, hx i]

/-- Every element of the common source has a simultaneous lift. -/
theorem jointCompleteQuotientGraph_lift {q : ℕ}
    (data : JointCompleteQuotientData G R q) (j : data.1) :
    ∃ r : Fin q → R, (r, (j : G)) ∈ jointCompleteQuotientGraph data := by
  choose r hr using fun i =>
    QuotientGroup.mk'_surjective (data.2 i).1.1 ((data.2 i).2.1 j)
  exact ⟨r, j, rfl, hr⟩

/-- Projection recovers the literal common source. -/
theorem jointCompleteQuotientGraph_source {q : ℕ}
    (data : JointCompleteQuotientData G R q) :
    (jointCompleteQuotientGraph data).map (MonoidHom.snd _ _) = data.1 := by
  ext g
  constructor
  · rintro ⟨x, ⟨j, hj, _⟩, hx⟩
    change x.2 = g at hx
    rw [← hx, ← hj]
    exact j.2
  · intro hg
    obtain ⟨r, hr⟩ := jointCompleteQuotientGraph_lift data ⟨g, hg⟩
    exact ⟨(r, g), hr, rfl⟩

/-- Projection to one retained target coordinate and the common source. -/
def jointCompleteQuotientProjection (q : ℕ) (i : Fin q) :
    ((Fin q → R) × G) →* R × G where
  toFun x := (x.1 i, x.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Each coordinate marginal is exactly its original quotient graph. -/
theorem jointCompleteQuotientGraph_marginal {q : ℕ}
    (data : JointCompleteQuotientData G R q) (i : Fin q) :
    (jointCompleteQuotientGraph data).map (jointCompleteQuotientProjection q i) =
      fusionQuotientGraph (QuotientGroup.mk' (data.2 i).1.1)
        data.1 (data.2 i).2.1 := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨j, hj, hy⟩, hxy⟩
    have hfirst : y.1 i = x.1 := congrArg Prod.fst hxy
    have hsecond : y.2 = x.2 := congrArg Prod.snd hxy
    exact ⟨j, hj.trans hsecond, by rw [← hfirst]; exact hy i⟩
  · rintro ⟨j, hj, hx⟩
    choose r hr using fun k =>
      QuotientGroup.mk'_surjective (data.2 k).1.1 ((data.2 k).2.1 j)
    let r' : Fin q → R := Function.update r i x.1
    refine ⟨(r', x.2), ?_, ?_⟩
    · refine ⟨j, hj, ?_⟩
      intro k
      by_cases hki : k = i
      · subst k
        simpa only [r', Function.update_self] using hx
      · simpa only [r', Function.update_of_ne hki] using hr k
    · apply Prod.ext
      · change r' i = x.1
        exact Function.update_self i x.1 r
      · rfl

/-- Insert one literal normal axis and quotient map into the full Goursat
classification with the source subgroup left unchanged. -/
def completeQuotientMapEncode (J : Subgroup G) :
    CompleteQuotientMap J R → FusionFullSubgroups R G := fun d =>
  (fusionFullGoursatEquiv (U := R) (G := G)).symm ⟨d.1, J, d.2⟩

theorem completeQuotientMapEncode_injective (J : Subgroup G) :
    Function.Injective (completeQuotientMapEncode (R := R) J) := by
  intro d e h
  have h' := congrArg (fusionFullGoursatEquiv (U := R) (G := G)) h
  simp only [completeQuotientMapEncode, Equiv.apply_symm_apply] at h'
  cases d with
  | mk N β =>
      cases e with
      | mk M γ =>
          cases h'
          rfl

theorem completeQuotientMapEncode_val (J : Subgroup G)
    (d : CompleteQuotientMap J R) :
    (completeQuotientMapEncode (R := R) J d).1 =
      fusionQuotientGraph (QuotientGroup.mk' d.1.1) J d.2.1 := by
  change ((fusionFullGoursatEquiv (U := R) (G := G)).symm
    ⟨d.1, J, d.2⟩).1 = _
  exact congrArg Subtype.val (fusionFullGoursatEquiv_symm d.1 J d.2)

/-- The simultaneous graph remembers the source, every literal normal axis,
and every onto quotient map. -/
theorem jointCompleteQuotientGraph_injective (q : ℕ) :
    Function.Injective
      (jointCompleteQuotientGraph (G := G) (R := R) (q := q)) := by
  rintro ⟨J, f⟩ ⟨K, g⟩ h
  have hJK : J = K := by
    calc
      J = (jointCompleteQuotientGraph ⟨J, f⟩).map (MonoidHom.snd _ _) :=
        (jointCompleteQuotientGraph_source ⟨J, f⟩).symm
      _ = (jointCompleteQuotientGraph ⟨K, g⟩).map (MonoidHom.snd _ _) := by rw [h]
      _ = K := jointCompleteQuotientGraph_source ⟨K, g⟩
  subst K
  have hfg : f = g := by
    funext i
    apply completeQuotientMapEncode_injective (R := R) J
    apply Subtype.ext
    rw [completeQuotientMapEncode_val, completeQuotientMapEncode_val]
    have hm := congrArg
      (fun H : Subgroup ((Fin q → R) × G) =>
        H.map (jointCompleteQuotientProjection q i)) h
    change
      (jointCompleteQuotientGraph ⟨J, f⟩).map
          (jointCompleteQuotientProjection q i) =
        (jointCompleteQuotientGraph ⟨J, g⟩).map
          (jointCompleteQuotientProjection q i) at hm
    rw [jointCompleteQuotientGraph_marginal ⟨J, f⟩ i,
      jointCompleteQuotientGraph_marginal ⟨J, g⟩ i] at hm
    exact hm
  subst g
  rfl

/-- The complete graph embedded in the faithful disjoint-block action. -/
def jointCompleteQuotientPermutationGraph {s : ℕ}
    (ρ : R →* Equiv.Perm (Fin s)) (b q : ℕ) :
    JointCompleteQuotientData (Equiv.Perm (Fin b)) R q →
      Subgroup (Equiv.Perm (Fin (b + q * s))) := fun data =>
  (jointCompleteQuotientGraph data).map (jointDisjointFiniteAction ρ b q)

theorem jointCompleteQuotientPermutationGraph_injective {s : ℕ}
    (ρ : R →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (b q : ℕ) :
    Function.Injective (jointCompleteQuotientPermutationGraph ρ b q) :=
  (Subgroup.map_injective (jointDisjointFiniteAction_injective ρ hρ b q)).comp
    (jointCompleteQuotientGraph_injective q)

/-- Exact cardinality of the shared-source parameter space. -/
theorem jointCompleteQuotientData_card [Finite G] [Finite R] (q : ℕ) :
    Nat.card (JointCompleteQuotientData G R q) =
      ∑ J : Subgroup G, completeQuotientCount (R := R) J ^ q := by
  rw [JointCompleteQuotientData, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro J _
  rw [Nat.card_fun, Nat.card_fin, completeQuotientMap_card]

/-- Strong ambient-group form of the moment injection, before choosing a
permutation representation of the retained quotient target. -/
theorem completeQuotientCount_moment_le_subgroup_product [Finite G] [Finite R]
    (q : ℕ) :
    ∑ J : Subgroup G, completeQuotientCount (R := R) J ^ q ≤
      Nat.card (Subgroup ((Fin q → R) × G)) := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite _
  have hcard := Nat.card_le_card_of_injective _
    (jointCompleteQuotientGraph_injective (G := G) (R := R) q)
  change Nat.card (JointCompleteQuotientData G R q) ≤
    Nat.card (Subgroup ((Fin q → R) × G)) at hcard
  rw [jointCompleteQuotientData_card] at hcard
  exact hcard

/-- Complete quotient moment over one actual source. Every power retains all
literal normal axes, including coincident and isomorphic quotient targets. -/
theorem completeQuotientCount_moment_le [Finite R] {s : ℕ}
    (ρ : R →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (b q : ℕ) :
    ∑ J : Subgroup (Equiv.Perm (Fin b)),
        completeQuotientCount (R := R) J ^ q ≤ subgroupCount (b + q * s) := by
  classical
  letI : Fintype (Subgroup (Equiv.Perm (Fin b))) := Fintype.ofFinite _
  have hcard := Nat.card_le_card_of_injective _
    (jointCompleteQuotientPermutationGraph_injective ρ hρ b q)
  change Nat.card
      (JointCompleteQuotientData (Equiv.Perm (Fin b)) R q) ≤
        subgroupCount (b + q * s) at hcard
  rw [jointCompleteQuotientData_card] at hcard
  exact hcard

end SymmetricSubgroupAsymptotics

end
