import SymmetricSubgroupAsymptotics.OriginalNonaffinePairFamiliesAllDegreeOrdinaryStep
import SymmetricSubgroupAsymptotics.SimpleModelMinimumIndexDegreeTransport
import SymmetricSubgroupAsymptotics.CFSGExceptionalThirtyTwoProperIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryAdmissibleIndexLower

/-! Literal proper-index bounds exclude every nonpaired Lie family from
local degrees at most seven. The result uses neither model group orders
nor a catalogue of permutation actions. The classification corollary keeps
the SAME actual simple factor, and leaves only exact Tits/sporadic tags. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleNonpairDegreeEight
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem degree_ge_eight_of_nonpair (j : CFSG.Index) (e : D.Simple ≃* j.Model)
    (hpair : ¬ PairFamily j) (hremaining : ¬ RemainingModel j) : 8 ≤ Nat.card X := by
  cases j with
  | cyclic p hp =>
      have hc : IsMulCommutative (CFSG.Index.cyclic p hp).Model := by
        change IsMulCommutative (Multiplicative (ZMod p))
        infer_instance
      exact (D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hc)).elim
  | alternating m hm => exact (hpair trivial).elim
  | A r q hr hs => exact (hpair trivial).elim
  | B r q hr => exact (hpair trivial).elim
  | C r q hr hs => exact (hpair trivial).elim
  | D r q hr => exact (hpair trivial).elim
  | suzuki m hm => exact (hpair trivial).elim
  | twistedA r q hr hs =>
      letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
      have hq := CFSGTwistedAQuadraticTrace.order_two_le q
      have hpow : 8 ≤ q.order^r := by
        by_cases htwo : r = 2
        · have hq3 : 3 ≤ q.order := by have hh := hs htwo; omega
          have hh : 9 ≤ q.order^2 := Nat.pow_le_pow_left hq3 2
          simpa only [htwo] using (show 8 ≤ q.order^2 by omega)
        · exact (Nat.pow_le_pow_left hq 3).trans
            (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega : 3 ≤ r))
      exact SimpleModelMinimumIndexDegreeTransport.degree_ge D e 8
        (fun H hH => hpow.trans
          (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_field_power_le_proper_index
            r hr q hs H hH))
  | twistedD r q hr =>
      letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := e.symm.isSimpleGroup
      have hq := CFSGTwistedAQuadraticTrace.order_two_le q
      have hleft : 4 ≤ q.order^(r-2) := (Nat.pow_le_pow_left hq 2).trans
        (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega : 2 ≤ r-2))
      have hright : 8 ≤ q.order^(r-1) := (Nat.pow_le_pow_left hq 3).trans
        (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega : 3 ≤ r-1))
      have hprod : 24 ≤ (q.order^(r-2)-1)*q.order^(r-1) := by
        calc
          24 = (4-1)*8 := by decide
          _ ≤ _ := Nat.mul_le_mul (by omega) hright
      exact SimpleModelMinimumIndexDegreeTransport.degree_ge D e 8
        (fun H hH => (by decide : 8 ≤ 24).trans (hprod.trans
          (CFSGReduction.typeTwistedD_point_radical_le_proper_index r hr q H hH)))
  | F4 q =>
      letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeFFour q)
      omega
  | G2 q hs =>
      letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeGTwo q hs)
      omega
  | E6 q =>
      letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeESix q)
      omega
  | E7 q =>
      letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeESeven q)
      omega
  | E8 q =>
      letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeEEight q)
      omega
  | twistedE6 q =>
      letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeTwistedESix q)
      omega
  | trialityD4 q =>
      letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeTriality q)
      omega
  | reeG2 m hm =>
      letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeReeGTwo m hm)
      omega
  | reeF4 m hm =>
      letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
      have hh := SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeReeFFour m hm)
      omega
  | tits => exact (hremaining trivial).elim
  | sporadic s => exact (hremaining trivial).elim

theorem pair_family_or_actual_remaining_of_degree_le_seven
    (hCFSG : CFSG.CFSGClassification) (hsmall : Nat.card X ≤ 7) :
    (∃ j : CFSG.Index, PairFamily j ∧ Nonempty (D.Simple ≃* j.Model)) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  obtain ⟨j,⟨e⟩⟩ := hCFSG.classify D.Simple
  by_cases hp : PairFamily j
  · exact Or.inl ⟨j,hp,⟨e⟩⟩
  by_cases hr : RemainingModel j
  · exact Or.inr ⟨j,hr,⟨e⟩⟩
  have hh := degree_ge_eight_of_nonpair D j e hp hr
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleNonpairDegreeEight
