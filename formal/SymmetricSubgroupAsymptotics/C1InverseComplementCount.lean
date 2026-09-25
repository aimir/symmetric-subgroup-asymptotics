import SymmetricSubgroupAsymptotics.C1InverseComplement

/-! # Exact reciprocal-weighted inverse-complement count
Each original oriented split character contributes exactly one after summing
its literal order-three witnesses with their actual reciprocal fibre size.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
variable {G : Type*} [Group G]

def ternaryWitnessCount (χ : PrimeCharacters 3 G) : ℕ := Nat.card (TernaryWitness χ)

theorem ternaryWitnessCount_pos [Finite G] {χ : PrimeCharacters 3 G}
    (hχ : TernarySplit χ) : 0 < ternaryWitnessCount χ := by
  obtain ⟨x,hx⟩ := (ternarySplit_iff_witness χ).mp hχ
  haveI : Nonempty (TernaryWitness χ) := ⟨⟨x,hx⟩⟩
  exact Nat.card_pos

theorem ternaryWitness_reciprocal_sum [Finite G] (χ : PrimeCharacters 3 G)
    (hχ : TernarySplit χ) :
    letI := Fintype.ofFinite (TernaryWitness χ)
    ∑ _x : TernaryWitness χ, ((ternaryWitnessCount χ : ℚ))⁻¹ = 1 := by
  letI := Fintype.ofFinite (TernaryWitness χ)
  have hn : (ternaryWitnessCount χ : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ternaryWitnessCount_pos hχ))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  change (ternaryWitnessCount χ : ℚ) * (ternaryWitnessCount χ : ℚ)⁻¹ = 1
  exact mul_inv_cancel₀ hn

abbrev TernarySurvivingPair
    (S : (Σ K : Subgroup G, PrimeCharacters 3 K) → Prop) :=
  {d : (Σ K : Subgroup G, PrimeCharacters 3 K) // TernarySplit d.2 ∧ S d}

def ternarySurvivingPairWitnessEquiv
    (S : (Σ K : Subgroup G, PrimeCharacters 3 K) → Prop) :
    (Σ d : TernarySurvivingPair S, TernaryWitness d.1.2) ≃
      {d : TernaryIncidence G // S ⟨d.1,d.2.1⟩} where
  toFun d := ⟨⟨d.1.1.1,d.1.1.2,d.2⟩,d.1.2.2⟩
  invFun d := ⟨⟨⟨d.1.1,d.1.2.1⟩,
    (ternarySplit_iff_witness _).mpr ⟨d.1.2.2.1,d.1.2.2.2⟩,d.2⟩,d.1.2.2⟩
  left_inv := by rintro ⟨⟨⟨K,χ⟩,h⟩,x⟩; rfl
  right_inv := by rintro ⟨⟨K,χ,x⟩,h⟩; rfl

instance [Finite G] : Finite (TernaryComplementChart G) :=
  Finite.of_equiv (TernaryIncidence G) ternaryInverseComplementEquiv

theorem ternaryChartIncidence_witnessCount (C : TernaryComplementChart G) :
    ternaryWitnessCount (ternaryChartIncidence C).2.1 = ternaryWitnessCount C.character := rfl

theorem ternaryIncidenceChart_witnessCount (d : TernaryIncidence G) :
    ternaryWitnessCount (ternaryIncidenceChart d).character =
      ternaryWitnessCount d.2.1 := by
  calc
    _ = ternaryWitnessCount (ternaryChartIncidence (ternaryIncidenceChart d)).2.1 :=
      (ternaryChartIncidence_witnessCount (ternaryIncidenceChart d)).symm
    _ = _ := congrArg (fun t : TernaryIncidence G => ternaryWitnessCount t.2.1)
      (ternaryChartIncidence_incidenceChart d)

/-- Exact incidence identity, before replacing the witness count by the
identical original coset count. Arbitrary survival predicates are retained. -/
theorem ternaryInverseComplement_reciprocal [Finite G]
    (S : (Σ K : Subgroup G, PrimeCharacters 3 K) → Prop) :
    letI := Fintype.ofFinite {C : TernaryComplementChart G // S ⟨C.source,C.character⟩}
    (Nat.card (TernarySurvivingPair S) : ℚ) =
      ∑ C : {C : TernaryComplementChart G // S ⟨C.source,C.character⟩},
        ((ternaryWitnessCount C.1.character : ℚ))⁻¹ := by
  letI := Fintype.ofFinite (TernarySurvivingPair S)
  letI (d : TernarySurvivingPair S) := Fintype.ofFinite (TernaryWitness d.1.2)
  letI := Fintype.ofFinite {d : TernaryIncidence G // S ⟨d.1,d.2.1⟩}
  letI := Fintype.ofFinite {C : TernaryComplementChart G // S ⟨C.source,C.character⟩}
  let e := (ternarySurvivingPairWitnessEquiv S).trans
    (ternaryInverseComplementSurvivalEquiv S)
  calc
    (Nat.card (TernarySurvivingPair S) : ℚ) =
        ∑ d : TernarySurvivingPair S, (1 : ℚ) := by simp [Nat.card_eq_fintype_card]
    _ = ∑ d : TernarySurvivingPair S,
        ∑ _x : TernaryWitness d.1.2, ((ternaryWitnessCount d.1.2 : ℚ))⁻¹ := by
      apply Finset.sum_congr rfl
      intro d _
      exact (ternaryWitness_reciprocal_sum d.1.2 d.2.1).symm
    _ = ∑ d : (Σ d : TernarySurvivingPair S, TernaryWitness d.1.2),
        ((ternaryWitnessCount d.1.1.2 : ℚ))⁻¹ := by rw [Fintype.sum_sigma]
    _ = _ := by
      apply Fintype.sum_equiv e
      intro d
      change ((ternaryWitnessCount d.1.1.2 : ℚ))⁻¹ =
        ((ternaryWitnessCount (ternaryIncidenceChart
          (ternarySurvivingPairWitnessEquiv S d).1).character : ℚ))⁻¹
      rw [ternaryIncidenceChart_witnessCount]
      rfl

end SymmetricSubgroupAsymptotics
