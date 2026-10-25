import SymmetricSubgroupAsymptotics.OriginalNonaffineTripleSmallDegreeOrdinaryStep
import SymmetricSubgroupAsymptotics.PrimitiveSocleJFourCompleteOrdinary

/-! Literal J4 has an order23 element, so any surviving local action below
degree32 has one socle factor and degree at least23. The uniform
three-generator recurrence pays every original top in that band. The
numerical callback already retained by the CFSG facade is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineJFourSmallBlockOrdinaryStep
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

include remaining in
theorem genRank_le_ceiling (i : block.Points) (hsmall : Nat.card block.Fibre < 32)
    (e : D.Simple ≃* (CFSG.Index.sporadic .j4).Model)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Finite (CFSG.Index.sporadic .j4).Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup (CFSG.Index.sporadic .j4).Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative (CFSG.Index.sporadic .j4).Model := by
    intro hc
    exact D.noncommutative ((isMulCommutative_congr e).mpr hc)
  have hp : ModelSufficientSimpleIndexBounds (.sporadic .j4) :=
    remaining (.sporadic .j4) hni (by trivial)
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  obtain ⟨horder,houter⟩ := sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell
  have hell23 : 23 ≤ ell := by
    have hd := SimpleLeastIndexStrictOrdinaryGenerators.card_dvd_factorial D.Simple ell hell
    have h23 : 23 ∣ Nat.card D.Simple := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSGJ4TwentyThreeDivisor.twenty_three_dvd_order hni
    by_contra h
    have hbad : 23 ∣ Nat.factorial 22 :=
      h23.trans (hd.trans (Nat.factorial_dvd_factorial (by omega)))
    exact (by decide : ¬ 23 ∣ Nat.factorial 22) hbad
  have hdegree := primitiveSocle_power_le_degree (show 5 ≤ ell by omega) horder (D.degreeForm hell)
  have hk : D.factorCount = 1 := by
    have hkpos := D.factorCount_pos
    by_contra h
    have hh := (Nat.pow_le_pow_left (show 6 ≤ ell by omega) D.factorCount).trans hdegree
    have hpow := (Nat.pow_le_pow_right (by decide : 0 < 6)
      (show 2 ≤ D.factorCount by omega)).trans hh
    change 36 ≤ Nat.card block.Fibre at hpow
    omega
  have hlo : 23 ≤ Nat.card block.Fibre :=
    hell23.trans (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)
  have hs : MarkedC4.genRank D.Simple ≤ 3 := by
    let e0 : D.Simple ≃* CFSG.Models.Presentations.J4.Model := e
    letI : Finite CFSG.Models.Presentations.J4.Model := Finite.of_equiv D.Simple e0.toEquiv
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e0]
    obtain ⟨S,hS,hcard⟩ := CFSGGeneration.j4_three_generators
    exact (MarkedC4.genRank_le hS).trans hcard
  exact OriginalNonaffineTripleSmallDegreeOrdinaryStep.genRank_le_ceiling J block D i
    (by omega) (by omega) hk hs hbelow ell hell houter

end SymmetricSubgroupAsymptotics.OriginalNonaffineJFourSmallBlockOrdinaryStep
