import SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinarySmallLocalFrontier
import SymmetricSubgroupAsymptotics.OriginalNonaffineTwistedDBlockOrdinaryStep
import SymmetricSubgroupAsymptotics.SimpleModelMinimumIndexDegreeTransport
import SymmetricSubgroupAsymptotics.CFSGExceptionalThirtyTwoProperIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryAdmissibleIndexLower

/-! The original nonaffine ordinary frontier retains only literal
Tits/sporadic tags or an actual unitary factor whose genuine q^rank index
bound lies below local32. Every other Lie/alternating tag is supplied by
proved generation or actual minimum-index exclusion, on the SAME factor.
This remains a reduction, not the global coarse permutation theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryUnitarySmallLocalFrontier
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

/-- The unitary residual retains its actual field/rank and index lower
bound, in addition to the literal original factor equivalence below. -/
def UnpaidModelAtLocalDegree (r : ℕ) (j : CFSG.Index) : Prop :=
  RemainingModel j ∨ (r < 32 ∧ match j with
    | .twistedA rank q _ _ => q.order^rank ≤ r
    | _ => False)

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (D : NonaffineData block.Component block.Fibre)

theorem genRank_le_ceiling_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n ∨
      ∃ j : CFSG.Index, UnpaidModelAtLocalDegree (Nat.card block.Fibre) j ∧
        Nonempty (D.Simple ≃* j.Model) := by
  rcases OriginalNonaffineOrdinarySmallLocalFrontier.genRank_le_ceiling_or_actual_remaining_model
    J block D hCFSG i hbelow with h | ⟨j,hj,⟨e⟩⟩
  · exact Or.inl h
  rcases hj with hremaining | ⟨hsmall,hnotpair⟩
  · exact Or.inr ⟨j,Or.inl hremaining,⟨e⟩⟩
  cases j with
  | cyclic p hp =>
    have hc : IsMulCommutative (CFSG.Index.cyclic p hp).Model := by
      change IsMulCommutative (Multiplicative (ZMod p))
      infer_instance
    exact (D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hc)).elim
  | alternating m hm => exact (hnotpair trivial).elim
  | A rank q hr hs => exact (hnotpair trivial).elim
  | B rank q hr => exact (hnotpair trivial).elim
  | C rank q hr hs => exact (hnotpair trivial).elim
  | D rank q hr => exact (hnotpair trivial).elim
  | suzuki m hm => exact (hnotpair trivial).elim
  | twistedD rank q hr =>
    exact Or.inl (OriginalNonaffineTwistedDBlockOrdinaryStep.genRank_le_ceiling
      J block D rank hr q e i hbelow)
  | twistedA rank q hr hs =>
    letI : IsSimpleGroup (CFSG.Models.TwistedA rank q) := e.symm.isSimpleGroup
    obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hm := CFSGReduction.leastProperIndex_of_mulEquiv e ell hell
    have hp := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_power_le_leastProperIndex
      rank hr q hs ell hm
    have hd := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
    exact Or.inr ⟨.twistedA rank q hr hs,Or.inr ⟨hsmall,hp.trans hd⟩,⟨e⟩⟩
  | F4 q =>
    letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeFFour q)
    omega
  | G2 q hs =>
    letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeGTwo q hs)
    omega
  | E6 q =>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeESix q)
    omega
  | E7 q =>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeESeven q)
    omega
  | E8 q =>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeEEight q)
    omega
  | twistedE6 q =>
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeTwistedESix q)
    omega
  | trialityD4 q =>
    letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeTriality q)
    omega
  | reeG2 m hm =>
    letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeReeGTwo m hm)
    omega
  | reeF4 m hm =>
    letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
    have hd := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
      (CFSGExceptionalThirtyTwoProperIndex.typeReeFFour m hm)
    omega
  | tits => exact Or.inr ⟨.tits,Or.inl trivial,⟨e⟩⟩
  | sporadic s => exact Or.inr ⟨.sporadic s,Or.inl trivial,⟨e⟩⟩

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (i : block.Points) (hbelow : SmallerTransitiveRankBound n) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling n) ∨
      ∃ j : CFSG.Index, UnpaidModelAtLocalDegree (Nat.card block.Fibre) j ∧
        Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model J block D hCFSG i hbelow with h | h
  · obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hF.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.OriginalNonaffineOrdinaryUnitarySmallLocalFrontier
