import SymmetricSubgroupAsymptotics.PrimitiveOrdinaryBoundedOneFactorCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleFFourAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeGTwoAllDegreeOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourAllDegreeOrdinary

/-! Every original primitive ordinary branch is filled except literal
Tits/sporadic models or a bounded, one-factor unitary action. The latter
retains its genuine field-power index and excludes the already proved
binary rank-three case. No model or bounded-action callback is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveOrdinaryUnitaryCFSGReduction
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

def RemainingAtDegree (n k : ℕ) (j : CFSG.Index) : Prop :=
  RemainingModel j ∨ (k = 1 ∧ n < 1024 ∧ match j with
    | .twistedA rank q _ _ => q.order^rank ≤ n ∧ ¬ (rank = 3 ∧ q.order = 2)
    | _ => False)

theorem genRank_le_ceiling_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 2 ≤ n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingAtDegree n D.factorCount j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases PrimitiveOrdinaryBoundedOneFactorCFSGReduction.genRank_le_ceiling_or_actual_remaining_model
    hCFSG n hn J hprimitive hbelow with h | ⟨D,j,hj,⟨e⟩⟩
  · exact Or.inl h
  rcases hj with hremaining | ⟨hk,hsmall,hunpaid⟩
  · exact Or.inr ⟨D,j,Or.inl hremaining,⟨e⟩⟩
  cases j with
  | cyclic p hp =>
    have hc : IsMulCommutative (CFSG.Index.cyclic p hp).Model := by
      change IsMulCommutative (Multiplicative (ZMod p))
      infer_instance
    exact (D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hc)).elim
  | alternating m hm => exact (hunpaid (Or.inl trivial)).elim
  | A rank q hr hs => exact (hunpaid (Or.inl trivial)).elim
  | B rank q hr => exact (hunpaid (Or.inl trivial)).elim
  | C rank q hr hs => exact (hunpaid (Or.inl trivial)).elim
  | D rank q hr => exact (hunpaid (Or.inl trivial)).elim
  | suzuki m hm => exact (hunpaid (Or.inl trivial)).elim
  | twistedD rank q hr => exact (hunpaid (Or.inr trivial)).elim
  | twistedA rank q hr hs =>
    letI : IsSimpleGroup (CFSG.Models.TwistedA rank q) := e.symm.isSimpleGroup
    obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
    have hp := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_power_le_leastProperIndex
      rank hr q hs ell hm
    have hd := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    refine Or.inr ⟨D,.twistedA rank q hr hs,Or.inr ⟨hk,hsmall,?_,?_⟩,⟨e⟩⟩
    · simpa only [Nat.card_fin] using hp.trans hd
    · exact fun h => hunpaid (Or.inr h)
  | F4 q =>
    exact Or.inl (by simpa only [Nat.card_fin] using
      PrimitiveSocleFFourAllDegreeOrdinary.genRank_le_ceiling D hk q e)
  | G2 q hs =>
    exact Or.inl (by simpa only [Nat.card_fin] using
      PrimitiveSocleGTwoAllDegreeOrdinary.genRank_le_ceiling D hk q hs e)
  | trialityD4 q =>
    exact Or.inl (by simpa only [Nat.card_fin] using
      PrimitiveSocleTrialityAllDegreeOrdinary.genRank_le_ceiling D hk q e)
  | reeG2 m hm =>
    exact Or.inl (by simpa only [Nat.card_fin] using
      PrimitiveSocleReeGTwoAllDegreeOrdinary.genRank_le_ceiling D hk m hm e)
  | reeF4 m hm =>
    exact Or.inl (by simpa only [Nat.card_fin] using
      PrimitiveSocleReeFFourAllDegreeOrdinary.genRank_le_ceiling D hk m hm e)
  | E6 q =>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 2048
      (CFSGReduction.typeE6_2048_le_index q)
    simp only [Nat.card_fin] at hd
    omega
  | E7 q =>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 2048
      (CFSGReduction.typeE7_2048_le_index q)
    simp only [Nat.card_fin] at hd
    omega
  | E8 q =>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 2048
      (CFSGReduction.typeE8_2048_le_index q)
    simp only [Nat.card_fin] at hd
    omega
  | twistedE6 q =>
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 2048
      (CFSGTwistedE6HeisenbergIndex.proper_index_ge_2048 q)
    simp only [Nat.card_fin] at hd
    omega
  | tits => exact Or.inr ⟨D,.tits,Or.inl trivial,⟨e⟩⟩
  | sporadic s => exact Or.inr ⟨D,.sporadic s,Or.inl trivial,⟨e⟩⟩

theorem exists_generating_finset_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : 2 ≤ n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (hbelow : SmallerTransitiveRankBound n) :
    (∃ U : Finset J, Subgroup.closure (U : Set J)=⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling n) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingAtDegree n D.factorCount j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model hCFSG n hn J hprimitive hbelow with h | h
  · obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨U,hgen,hU.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.PrimitiveOrdinaryUnitaryCFSGReduction
