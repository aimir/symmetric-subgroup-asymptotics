import SymmetricSubgroupAsymptotics.TraceyOrdinaryGlobalFiniteModelCounterexample
import SymmetricSubgroupAsymptotics.CFSGReeFFourCompleteSufficientSimpleIndex
import SymmetricSubgroupAsymptotics.SimpleLeastIndexFiveRecognition

/-! The numerical callback ALREADY retained by the ReeF4-outer facade
eliminates actual multifactor primitive coarse failures and all actual
nonaffine block failures with fibre degree at least 32. The same original
group, socle data, equivalence and block map remain in every surviving
witness. No ordinary-rank callback or global Tracey/MN bound is added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryRetainedIndexResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open TransitiveOrdinaryLieCFSGReduction CFSGReduction

private theorem model_packet_of_retained
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model]
    (hn : ¬ IsMulCommutative i.Model) : ModelSufficientSimpleIndexBounds i := by
  rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining i hn with hp | hi
  · exact hp
  · cases i <;> try { exact False.elim hi }
    case tits => exact remaining .tits hn (by trivial)
    case sporadic s hfinite hsimple => exact remaining (.sporadic s) hn (by trivial)

private theorem packet_of_retained
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i) : SufficientSimpleIndexBounds := by
  intro G _ _ _ hn
  obtain ⟨i, ⟨e⟩⟩ := hCFSG.classify G
  letI : Finite i.Model := Finite.of_equiv G e.toEquiv
  letI : IsSimpleGroup i.Model := e.symm.isSimpleGroup
  have hni : ¬ IsMulCommutative i.Model := by
    intro hc
    exact hn ((isMulCommutative_congr e).mpr hc)
  exact sufficientSimpleIndexBounds_of_mulEquiv e (model_packet_of_retained remaining i hni)

/-- All multiplicities at least two are paid by the same actual index
packet. Below degree 32 the actual least index must be five, so its
faithful coset action supplies the proved A5 generating pair. -/
theorem multifactor_genRank_le_ceiling_of_actual_packet
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X) (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (hk : 2 ≤ D.factorCount) (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)))
    (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  by_cases h32 : 32 ≤ Nat.card X
  · exact PrimitiveSocleSmallMultipleStrictOrdinary.genRank_le_ceiling
      D ell hbelow hell hk horder h32 houter
  · have hell5 : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
      (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) hell.1
    have hdegree := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
    have hsq : ell^2 ≤ Nat.card X :=
      (Nat.pow_le_pow_right (by omega : 0 < ell) hk).trans hdegree
    have he : ell = 5 := by
      have hell6 : ell < 6 := by
        by_contra h6
        have hp := Nat.pow_le_pow_left (show 6 ≤ ell by omega) 2
        norm_num at hp
        omega
      omega
    have hsimple : MarkedC4.genRank D.Simple ≤ 2 := by
      subst ell
      exact SimpleLeastIndexFiveRecognition.genRank_le_two D.Simple D.noncommutative hell horder
    exact PrimitiveSocleBoundedMultiplePairOrdinary.genRank_le_ceiling
      D ell hbelow hell hk horder houter hsimple

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

/-- The actual remaining witnesses are strictly narrower: primitive
failures have one factor; imprimitive failures have local degree below
32. Their original finite-model equivalences are retained literally. -/
def NarrowActualFiniteModelResidual : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model)) ∨
  (¬ MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre < 32 ∧
        ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model))

theorem narrow_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i)
    (hn : 2 ≤ n) (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : NarrowActualFiniteModelResidual J := by
  have hindex := packet_of_retained hCFSG remaining
  have hres := TraceyOrdinaryGlobalFiniteModelCounterexample.minimal_counterexample_has_actual_finite_model
    hCFSG n hn J hbad hbelow
  rcases hres with ⟨hprimitive, D, i, hi, he⟩ | ⟨hprimitive, x₀, block, D, i, hi, he⟩
  · left
    refine ⟨hprimitive, D, ?_, i, hi, he⟩
    by_contra hk
    letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
      (by simpa only [Nat.card_fin] using (show 1 < n by omega))
    letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
    obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
    obtain ⟨horder, houter⟩ := hindex D.Simple D.noncommutative ell hell
    have hbound := multifactor_genRank_le_ceiling_of_actual_packet D ell hell
      (by have hpos := D.factorCount_pos; omega) horder houter
      (by simpa only [Nat.card_fin] using hbelow)
    exact not_lt_of_ge (by simpa only [Nat.card_fin] using hbound) hbad
  · right
    refine ⟨hprimitive, x₀, block, D, ?_, i, hi, he⟩
    by_contra hsmall
    letI : Fintype block.Points := Fintype.ofFinite _
    obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
    obtain ⟨horder, houter⟩ := hindex D.Simple D.noncommutative ell hell
    have hbound := OriginalNonaffineThirtyTwoOrdinaryStep.genRank_le_ceiling_of_actual_packet
      J block D block.base (by omega) hbelow ell hell horder houter
    exact not_lt_of_ge hbound hbad

theorem traceyPermutation_or_actual_minimal_narrow_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterReeFFourOuter i →
        ModelBoundsAfterReeFFourIndexSquare i) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2 ≤ n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n < MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ NarrowActualFiniteModelResidual J := by
  rcases TraceyOrdinaryGlobalFiniteModelCounterexample.traceyPermutation_or_actual_minimal_finite_model
    hCFSG with h | ⟨n, hn, J, ht, hbad, hbelow, _⟩
  · exact Or.inl h
  · letI := ht
    exact Or.inr ⟨n, hn, J, ht, hbad, hbelow,
      narrow_residual_of_failed_coarse J hCFSG remaining hn hbad hbelow⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryRetainedIndexResidual
