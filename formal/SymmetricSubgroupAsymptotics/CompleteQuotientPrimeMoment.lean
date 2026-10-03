import SymmetricSubgroupAsymptotics.CompleteQuotientMoment
import SymmetricSubgroupAsymptotics.PrimeRankWeightedTail

/-!
# Complete quotient maps with same-source prime markers

The complete quotient-map moment and the prime-character marker moment must
be used jointly in the affine central row.  This file gives the literal graph
injection.  Every coordinate retains its normal axis, quotient epimorphism,
and prime-character homomorphism on one unchanged source subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {G R M : Type*} [Group G] [Group R] [Group M]

/-- A tuple of complete quotient maps and marker maps sharing one source. -/
abbrev JointCompleteMarkedData
    (G R M : Type*) [Group G] [Group R] [Group M] (q : ℕ) :=
  Σ J : Subgroup G,
    Fin q → (CompleteQuotientMap J R × (J →* M))

/-- The simultaneous literal quotient/marker graph. -/
def jointCompleteMarkedGraph {q : ℕ}
    (data : JointCompleteMarkedData G R M q) :
    Subgroup ((Fin q → R × M) × G) where
  carrier := {x | ∃ j : data.1, (j : G) = x.2 ∧ ∀ i,
    QuotientGroup.mk' (data.2 i).1.1.1 (x.1 i).1 =
        (data.2 i).1.2.1 j ∧
      (x.1 i).2 = (data.2 i).2 j}
  one_mem' := ⟨1, rfl, by intro i; simp⟩
  mul_mem' := by
    rintro x y ⟨j, hj, hx⟩ ⟨k, hk, hy⟩
    refine ⟨j * k, ?_, ?_⟩
    · change (j : G) * (k : G) = x.2 * y.2
      rw [hj, hk]
    · intro i
      constructor
      · change QuotientGroup.mk' (data.2 i).1.1.1
            ((x.1 i).1 * (y.1 i).1) =
          (data.2 i).1.2.1 (j * k)
        rw [map_mul, map_mul, (hx i).1, (hy i).1]
      · change (x.1 i).2 * (y.1 i).2 = (data.2 i).2 (j * k)
        rw [map_mul, (hx i).2, (hy i).2]
  inv_mem' := by
    rintro x ⟨j, hj, hx⟩
    refine ⟨j⁻¹, ?_, ?_⟩
    · change (j : G)⁻¹ = x.2⁻¹
      rw [hj]
    · intro i
      constructor
      · change QuotientGroup.mk' (data.2 i).1.1.1 (x.1 i).1⁻¹ =
          (data.2 i).1.2.1 j⁻¹
        rw [map_inv, map_inv, (hx i).1]
      · change (x.1 i).2⁻¹ = (data.2 i).2 j⁻¹
        rw [map_inv, (hx i).2]

/-- Every source element has a simultaneous lift in the marked graph. -/
theorem jointCompleteMarkedGraph_lift {q : ℕ}
    (data : JointCompleteMarkedData G R M q) (j : data.1) :
    ∃ x : Fin q → R × M,
      (x, (j : G)) ∈ jointCompleteMarkedGraph data := by
  choose r hr using fun i =>
    QuotientGroup.mk'_surjective (data.2 i).1.1.1
      ((data.2 i).1.2.1 j)
  exact ⟨fun i => (r i, (data.2 i).2 j), j, rfl,
    fun i => ⟨hr i, rfl⟩⟩

/-- Projection recovers the literal common source. -/
theorem jointCompleteMarkedGraph_source {q : ℕ}
    (data : JointCompleteMarkedData G R M q) :
    (jointCompleteMarkedGraph data).map (MonoidHom.snd _ _) = data.1 := by
  ext g
  constructor
  · rintro ⟨x, ⟨j, hj, _⟩, hx⟩
    change x.2 = g at hx
    rw [← hx, ← hj]
    exact j.2
  · intro hg
    obtain ⟨x, hx⟩ := jointCompleteMarkedGraph_lift data ⟨g, hg⟩
    exact ⟨(x, g), hx, rfl⟩

/-- Projection to the quotient graph in one retained coordinate. -/
def jointCompleteMarkedQuotientProjection (q : ℕ) (i : Fin q) :
    ((Fin q → R × M) × G) →* R × G where
  toFun x := ((x.1 i).1, x.2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The quotient marginal is exactly the original literal quotient graph. -/
theorem jointCompleteMarkedGraph_quotient_marginal {q : ℕ}
    (data : JointCompleteMarkedData G R M q) (i : Fin q) :
    (jointCompleteMarkedGraph data).map
        (jointCompleteMarkedQuotientProjection q i) =
      fusionQuotientGraph (QuotientGroup.mk' (data.2 i).1.1.1)
        data.1 (data.2 i).1.2.1 := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨j, hj, hy⟩, hxy⟩
    have hfirst : (y.1 i).1 = x.1 := congrArg Prod.fst hxy
    have hsecond : y.2 = x.2 := congrArg Prod.snd hxy
    exact ⟨j, hj.trans hsecond, by rw [← hfirst]; exact (hy i).1⟩
  · rintro ⟨j, hj, hx⟩
    obtain ⟨y, hy⟩ := jointCompleteMarkedGraph_lift data j
    rcases hy with ⟨j₀, hj₀, hy⟩
    have hj₀j : j₀ = j := Subtype.ext hj₀
    subst j₀
    let y' : Fin q → R × M :=
      Function.update y i (x.1, (data.2 i).2 j)
    refine ⟨(y', x.2), ?_, ?_⟩
    · refine ⟨j, hj, ?_⟩
      intro k
      by_cases hki : k = i
      · subst k
        simp only [y', Function.update_self]
        exact ⟨hx, True.intro⟩
      · simpa only [y', Function.update_of_ne hki] using hy k
    · apply Prod.ext
      · change (y' i).1 = x.1
        simp [y']
      · rfl

/-- The graph determines the source, every normal axis and quotient map,
and every marker map. -/
theorem jointCompleteMarkedGraph_injective (q : ℕ) :
    Function.Injective
      (jointCompleteMarkedGraph (G := G) (R := R) (M := M) (q := q)) := by
  rintro ⟨J, f⟩ ⟨K, g⟩ h
  have hJK : J = K := by
    calc
      J = (jointCompleteMarkedGraph ⟨J, f⟩).map (MonoidHom.snd _ _) :=
        (jointCompleteMarkedGraph_source ⟨J, f⟩).symm
      _ = (jointCompleteMarkedGraph ⟨K, g⟩).map (MonoidHom.snd _ _) := by
        rw [h]
      _ = K := jointCompleteMarkedGraph_source ⟨K, g⟩
  subst K
  have hfg : f = g := by
    funext i
    apply Prod.ext
    · apply completeQuotientMapEncode_injective (R := R) J
      apply Subtype.ext
      rw [completeQuotientMapEncode_val, completeQuotientMapEncode_val]
      have hm := congrArg
        (fun H : Subgroup ((Fin q → R × M) × G) =>
          H.map (jointCompleteMarkedQuotientProjection q i)) h
      simpa only [jointCompleteMarkedGraph_quotient_marginal] using hm
    · apply MonoidHom.ext
      intro j
      obtain ⟨x, hx⟩ := jointCompleteMarkedGraph_lift ⟨J, f⟩ j
      have hx' : (x, (j : G)) ∈ jointCompleteMarkedGraph ⟨J, g⟩ := h ▸ hx
      rcases hx with ⟨j₁, hj₁, hf⟩
      rcases hx' with ⟨j₂, hj₂, hg⟩
      have hj₁' : j₁ = j := Subtype.ext hj₁
      have hj₂' : j₂ = j := Subtype.ext hj₂
      subst j₁
      subst j₂
      exact (hf i).2.symm.trans (hg i).2
  subst g
  rfl

/-- Marked complete quotient graphs in the faithful disjoint action. -/
def jointCompleteMarkedPermutationGraph
    {s t : ℕ}
    (ρ : R →* Equiv.Perm (Fin s))
    (μ : M →* Equiv.Perm (Fin t)) (b q : ℕ) :
    JointCompleteMarkedData (Equiv.Perm (Fin b)) R M q →
      Subgroup (Equiv.Perm (Fin (b + q * (s + t)))) := fun data =>
  (jointCompleteMarkedGraph data).map
    (jointDisjointFiniteAction (jointAuxiliaryAction ρ μ) b q)

theorem jointCompleteMarkedPermutationGraph_injective
    {s t : ℕ}
    (ρ : R →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (μ : M →* Equiv.Perm (Fin t)) (hμ : Function.Injective μ)
    (b q : ℕ) :
    Function.Injective (jointCompleteMarkedPermutationGraph ρ μ b q) :=
  (Subgroup.map_injective
    (jointDisjointFiniteAction_injective
      (jointAuxiliaryAction ρ μ)
      (jointAuxiliaryAction_injective ρ hρ μ hμ) b q)).comp
    (jointCompleteMarkedGraph_injective q)

/-- Exact cardinality of the complete quotient/marker parameter space. -/
theorem jointCompleteMarkedData_card
    [Finite G] [Finite R] [Finite M] (q : ℕ) :
    Nat.card (JointCompleteMarkedData G R M q) =
      ∑ J : Subgroup G,
        (completeQuotientCount (R := R) J * Nat.card (J →* M)) ^ q := by
  letI (J : Subgroup G) : Finite (J →* M) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI (J : Subgroup G) : Finite (CompleteQuotientMap J R) := inferInstance
  rw [JointCompleteMarkedData, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro J _
  rw [Nat.card_fun, Nat.card_fin, Nat.card_prod,
    completeQuotientMap_card]

/-- Complete quotient maps and `c` prime-character columns have one exact
same-source moment in degree `b + q * (s + p*c)`. -/
theorem completeQuotientPrimeWeight_moment_le
    (p : ℕ) [Fact p.Prime] [Finite R]
    {s : ℕ} (ρ : R →* Equiv.Perm (Fin s))
    (hρ : Function.Injective ρ) (b c q : ℕ) :
    ∑ J : Subgroup (Equiv.Perm (Fin b)),
        (completeQuotientCount (R := R) J *
          p ^ (c * Module.finrank (ZMod p) (PrimeCharacters p J))) ^ q ≤
      subgroupCount (b + q * (s + p * c)) := by
  classical
  let M := Multiplicative (Fin c → ZMod p)
  letI : Group M := inferInstance
  letI : Finite M := inferInstance
  have hcard := Nat.card_le_card_of_injective _
    (jointCompleteMarkedPermutationGraph_injective ρ hρ
      (primeMarkerFiniteAction p c)
      (primeMarkerFiniteAction_injective p c) b q)
  change Nat.card
      (JointCompleteMarkedData (Equiv.Perm (Fin b)) R M q) ≤
        subgroupCount (b + q * (s + p * c)) at hcard
  rw [jointCompleteMarkedData_card] at hcard
  simpa only [M, primeAbelianizationGroupHom_card p,
    Module.finrank_pi, Fintype.card_fin, Nat.mul_comm] using hcard

end SymmetricSubgroupAsymptotics

end
