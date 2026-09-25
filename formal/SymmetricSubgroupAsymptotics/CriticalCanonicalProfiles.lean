import SymmetricSubgroupAsymptotics.CriticalOccurrenceQuotients
import SymmetricSubgroupAsymptotics.CriticalProfileEstimates
import SymmetricSubgroupAsymptotics.ProductCanonicalLifts

/-! Uniform canonical and complete-model estimates on the actual critical profiles. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

def criticalOccurrenceChart (p : CriticalProfile) :
    (Fin p.rank → ZMod 2) ≃ₗ[ZMod 2]
      (∀ x : CriticalProfileOccurrence p, Fin (criticalOccurrenceRank p x) → ZMod 2) :=
  LinearEquiv.ofFinrankEq (R := ZMod 2) _ _ (by
    rw [Module.finrank_pi, Fintype.card_fin, Module.finrank_pi_fintype]
    simp only [Module.finrank_pi, Fintype.card_fin]
    exact (criticalOccurrenceRank_sum p).symm)

def criticalOccurrenceProductQuotient (p : CriticalProfile) :
    (∀ x : CriticalProfileOccurrence p, CriticalOccurrenceGroup p x) →*
      Multiplicative (Fin p.rank → ZMod 2) :=
  productBinaryQuotient (CriticalOccurrenceGroup p) (criticalOccurrenceRank p)
    (criticalOccurrenceChart p) (criticalOccurrenceQuotient p)

abbrev CriticalFullOccurrenceSubgroups (p : CriticalProfile) :=
  {H : Subgroup (∀ x : CriticalProfileOccurrence p, CriticalOccurrenceGroup p x) //
    ∀ x, H.map (Pi.evalMonoidHom (CriticalOccurrenceGroup p) x) = ⊤}

/-- Flattening all original occurrences preserves exactly the full projection
condition, including each entire V4 coordinate. -/
def criticalModelSubgroupsEquivOccurrences (p : CriticalProfile) :
    CriticalModelSubgroups p ≃ CriticalFullOccurrenceSubgroups p :=
  (criticalModelSubgroupsEquivProduct p).trans
    { toFun := fun H ↦ ⟨H.1.map (criticalProfileOccurrenceEquiv p).toMonoidHom, by
        rintro ⟨i,j⟩
        apply top_unique
        intro u _
        obtain ⟨g,hg⟩ := H.2 i j u
        exact ⟨criticalProfileOccurrenceEquiv p g.1, ⟨g.1,g.2,rfl⟩, hg⟩⟩
      invFun := fun H ↦ ⟨H.1.comap (criticalProfileOccurrenceEquiv p).toMonoidHom, by
        intro i j u
        have hu : u ∈ H.1.map (Pi.evalMonoidHom (CriticalOccurrenceGroup p) ⟨i,j⟩) := by
          rw [H.2 ⟨i,j⟩]
          exact Subgroup.mem_top _
        obtain ⟨g,hg,he⟩ := hu
        refine ⟨⟨(criticalProfileOccurrenceEquiv p).symm g, ?_⟩, he⟩
        change criticalProfileOccurrenceEquiv p ((criticalProfileOccurrenceEquiv p).symm g) ∈ H.1
        simpa using hg⟩
      left_inv := fun H ↦ Subtype.ext
        (Subgroup.comap_map_eq_self_of_injective (criticalProfileOccurrenceEquiv p).injective H.1)
      right_inv := fun H ↦ Subtype.ext
        (Subgroup.map_comap_eq_self_of_surjective (criticalProfileOccurrenceEquiv p).surjective H.1) }

theorem criticalProfile_kernel_transport (p : CriticalProfile)
    (H : Subgroup (OrbitProfileProductGroup p.multiplicity criticalActionSubgroup)) :
    (criticalProductQuotient p.abelianRank (criticalProfileNonabelianChoice p)).ker ≤
      H.map (criticalProfileProductEquiv p).toMonoidHom ↔
    (criticalOccurrenceProductQuotient p).ker ≤ H.map (criticalProfileOccurrenceEquiv p).toMonoidHom := by
  have hk :
      (criticalProductQuotient p.abelianRank (criticalProfileNonabelianChoice p)).ker.comap
        (criticalProfileProductEquiv p).toMonoidHom =
      (criticalOccurrenceProductQuotient p).ker.comap (criticalProfileOccurrenceEquiv p).toMonoidHom := by
    ext g
    change criticalProfileProductEquiv p g ∈
      (criticalProductQuotient p.abelianRank (criticalProfileNonabelianChoice p)).ker ↔
        criticalProfileOccurrenceEquiv p g ∈ (criticalOccurrenceProductQuotient p).ker
    rw [criticalProfileProductEquiv_mem_kernel_iff]
    exact (productBinaryQuotient_mem_ker (CriticalOccurrenceGroup p) (criticalOccurrenceRank p)
      (criticalOccurrenceChart p) (criticalOccurrenceQuotient p) _).symm
  rw [← Subgroup.comap_le_comap_of_surjective
      (f := (criticalProfileProductEquiv p).toMonoidHom) (criticalProfileProductEquiv p).surjective,
    ← Subgroup.comap_le_comap_of_surjective
      (f := (criticalProfileOccurrenceEquiv p).toMonoidHom) (criticalProfileOccurrenceEquiv p).surjective,
    Subgroup.comap_map_eq_self_of_injective (criticalProfileProductEquiv p).injective,
    Subgroup.comap_map_eq_self_of_injective (criticalProfileOccurrenceEquiv p).injective, hk]

theorem criticalModelIsCanonical_iff_occurrences (p : CriticalProfile) (H : CriticalModelSubgroups p) :
    CriticalModelIsCanonical p H ↔
      (criticalOccurrenceProductQuotient p).ker ≤ (criticalModelSubgroupsEquivOccurrences p H).1 := by
  exact criticalProfile_kernel_transport p (criticalModelSubgroupsEquivProduct p H).1

/-- The canonical family is an exact bijection of original subgroups, not a
numerical identification with a Gaussian count. -/
def criticalCanonicalModelEquivOccurrences (p : CriticalProfile) :
    CriticalCanonicalModelSubgroups p ≃
      {H : Subgroup (∀ x : CriticalProfileOccurrence p, CriticalOccurrenceGroup p x) //
        (criticalOccurrenceProductQuotient p).ker ≤ H ∧
          ∀ x, H.map (Pi.evalMonoidHom (CriticalOccurrenceGroup p) x) = ⊤} :=
  ((criticalModelSubgroupsEquivOccurrences p).subtypeEquiv
    (p := CriticalModelIsCanonical p)
    (q := fun H : CriticalFullOccurrenceSubgroups p ↦
      (criticalOccurrenceProductQuotient p).ker ≤ H.1)
    (criticalModelIsCanonical_iff_occurrences p)).trans
    { toFun := fun H ↦ ⟨H.1.1,H.2,H.1.2⟩
      invFun := fun H ↦ ⟨⟨H.1,H.2.2⟩,H.2.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- One constant and threshold work for every actual critical profile. -/
theorem criticalCanonicalModelSubgroups_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ p : CriticalProfile, N ≤ p.rank →
      |(Nat.card (CriticalCanonicalModelSubgroups p) : ℝ) / binarySubspaceCount p.rank - 1| ≤
        C * p.rank * (2 : ℝ) ^ (-(p.rank : ℝ) / 2) := by
  obtain ⟨C,hC,N,hN,hbound⟩ := productCanonical_full_projection_relative_error
  refine ⟨C,hC,N,hN,?_⟩
  intro p hp
  have h := hbound p.rank hp (CriticalOccurrenceGroup p) (criticalOccurrenceRank p)
    (criticalOccurrenceChart p) (criticalOccurrenceQuotient p)
    (criticalOccurrenceQuotient_surjective p) (fun x ↦ (criticalOccurrenceRank_bounds p x).2)
    (criticalOccurrence_card_le_rank p)
  rw [Nat.card_congr (criticalCanonicalModelEquivOccurrences p)]
  exact h

/-- Complete actual-model estimate: the canonical full-projection deficit
and the noncanonical incidence contribution have independent, uniform losses. -/
theorem criticalModelSubgroups_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ p : CriticalProfile, N ≤ p.rank →
      |(Nat.card (CriticalModelSubgroups p) : ℝ) / (binaryGaussianSum p.rank : ℝ) - 1| ≤
        C * ((p.rank : ℝ) * (2 : ℝ) ^ (-(p.rank : ℝ) / 2) +
          (2 : ℝ) ^ (-((p.c2 : ℝ) / 2 + p.v4 + p.e8))) := by
  obtain ⟨C,hC,N,hN,hcanonical⟩ := criticalCanonicalModelSubgroups_relative_error
  let E : ℝ := exceptionalGaussianConstant / eulerProduct
  have hE : 0 < E := div_pos exceptionalGaussianConstant_pos euler_positive
  refine ⟨C + E, add_pos hC hE, N, hN, ?_⟩
  intro p hp
  let G : ℝ := binaryGaussianSum p.rank
  have hG : 0 < G := by
    dsimp [G]
    exact_mod_cast binaryGaussianSum_pos p.rank
  have hcast : (binarySubspaceCount p.rank : ℝ) = G := by
    dsimp [G]
    exact_mod_cast binarySubspaceCount_eq_gaussianSum p.rank
  have hc := hcanonical p hp
  rw [hcast] at hc
  have he : (Nat.card (CriticalNoncanonicalModelSubgroups p) : ℝ) / G ≤
      E * (2 : ℝ) ^ (-((p.c2 : ℝ) / 2 + p.v4 + p.e8)) := by
    apply (div_le_iff₀ hG).mpr
    simpa only [E, G, mul_assoc, mul_comm, mul_left_comm] using
      criticalNoncanonicalModelSubgroups_card_le p
  have hn : 0 ≤ (Nat.card (CriticalNoncanonicalModelSubgroups p) : ℝ) / G :=
    div_nonneg (Nat.cast_nonneg _) hG.le
  have hsplit : (Nat.card (CriticalModelSubgroups p) : ℝ) / G - 1 =
      ((Nat.card (CriticalCanonicalModelSubgroups p) : ℝ) / G - 1) +
        (Nat.card (CriticalNoncanonicalModelSubgroups p) : ℝ) / G := by
    rw [criticalModelSubgroups_card_split, Nat.cast_add]
    ring
  change |(Nat.card (CriticalModelSubgroups p) : ℝ) / G - 1| ≤ _
  rw [hsplit]
  calc
    _ ≤ |(Nat.card (CriticalCanonicalModelSubgroups p) : ℝ) / G - 1| +
        |(Nat.card (CriticalNoncanonicalModelSubgroups p) : ℝ) / G| := abs_add_le _ _
    _ ≤ C * p.rank * (2 : ℝ) ^ (-(p.rank : ℝ) / 2) +
        E * (2 : ℝ) ^ (-((p.c2 : ℝ) / 2 + p.v4 + p.e8)) := by
      rw [abs_of_nonneg hn]
      exact add_le_add hc he
    _ ≤ _ := by
      have ht : 0 ≤ (p.rank : ℝ) * (2 : ℝ) ^ (-(p.rank : ℝ) / 2) := by positivity
      have hu : 0 ≤ (2 : ℝ) ^ (-((p.c2 : ℝ) / 2 + p.v4 + p.e8)) := by positivity
      nlinarith [mul_nonneg hE.le ht, mul_nonneg hC.le hu]

end SymmetricSubgroupAsymptotics
