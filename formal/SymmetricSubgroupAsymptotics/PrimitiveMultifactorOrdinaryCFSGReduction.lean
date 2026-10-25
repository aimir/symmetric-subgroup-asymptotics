import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallMultipleStrictOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSoclePairFamiliesCompleteOrdinary
import SymmetricSubgroupAsymptotics.CFSGExceptionalThirtyTwoProperIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryAdmissibleIndexLower
import SymmetricSubgroupAsymptotics.SimpleModelMinimumIndexDegreeTransport

/-! The whole primitive multifactor ordinary branch at every degree.
The bounded range uses strict-coset induction, and the genuinely tiny
range either has a proved pair family or is excluded by an actual index.
Only literal Tits/sporadic factors remain. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveMultifactorOrdinaryCFSGReduction
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

theorem model_index_six_or_pair_or_remaining (j : CFSG.Index)
    [hfinite : Finite j.Model] [hsimple : IsSimpleGroup j.Model]
    (hn : ¬ IsMulCommutative j.Model) :
    (∀ H : Subgroup j.Model, H≠⊤ → 6≤H.index) ∨ PairFamily j ∨ RemainingModel j := by
  cases j with
  | cyclic p hp =>
    exact (hn (inferInstance : IsMulCommutative (Multiplicative (ZMod p)))).elim
  | alternating m hm => exact Or.inr (Or.inl trivial)
  | A r q hr hs => exact Or.inr (Or.inl trivial)
  | B r q hr => exact Or.inr (Or.inl trivial)
  | C r q hr hs => exact Or.inr (Or.inl trivial)
  | D r q hr => exact Or.inr (Or.inl trivial)
  | suzuki m hm => exact Or.inr (Or.inl trivial)
  | twistedA r q hr hs =>
    letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := hsimple
    have hq := CFSGTwistedAQuadraticTrace.order_two_le q
    have hp : 8≤q.order^r := by
      by_cases htwo : r=2
      · have hq3 : 3≤q.order := by have hh := hs htwo; omega
        have h := Nat.pow_le_pow_left hq3 2
        subst r
        norm_num at h
        omega
      · calc
          8 = 2^3 := by decide
          _ ≤ q.order^3 := Nat.pow_le_pow_left hq 3
          _ ≤ q.order^r := Nat.pow_le_pow_right (by omega) (by omega)
    exact Or.inl (fun H hH => (by decide : 6≤8).trans (hp.trans
      (CFSGTwistedAUnitaryCoordinates.twistedA_admissible_field_power_le_proper_index r hr q hs H hH)))
  | twistedD r q hr =>
    letI : IsSimpleGroup (CFSG.Models.TwistedD r q) := hsimple
    have hq := CFSGTwistedAQuadraticTrace.order_two_le q
    have hq0 : 0<q.order := by omega
    have ha : 4≤q.order^(r-2) := by
      calc
        4 = 2^2 := by decide
        _ ≤ q.order^2 := Nat.pow_le_pow_left hq 2
        _ ≤ q.order^(r-2) := Nat.pow_le_pow_right hq0 (by omega)
    have hb : 8≤q.order^(r-1) := by
      calc
        8 = 2^3 := by decide
        _ ≤ q.order^3 := Nat.pow_le_pow_left hq 3
        _ ≤ q.order^(r-1) := Nat.pow_le_pow_right hq0 (by omega)
    have hp : 24≤(q.order^(r-2)-1)*q.order^(r-1) :=
      Nat.mul_le_mul (show 3≤q.order^(r-2)-1 by omega) hb
    exact Or.inl (fun H hH => (by decide : 6≤24).trans (hp.trans
      (CFSGReduction.typeTwistedD_point_radical_le_proper_index r hr q H hH)))
  | F4 q =>
    letI : IsSimpleGroup (CFSG.Models.F4 q) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeFFour q H hH))
  | G2 q hs =>
    letI : IsSimpleGroup (CFSG.Models.G2 q) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeGTwo q hs H hH))
  | E6 q =>
    letI : IsSimpleGroup (CFSG.Models.E6 q) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeESix q H hH))
  | E7 q =>
    letI : IsSimpleGroup (CFSG.Models.E7 q) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeESeven q H hH))
  | E8 q =>
    letI : IsSimpleGroup (CFSG.Models.E8 q) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeEEight q H hH))
  | twistedE6 q =>
    letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeTwistedESix q H hH))
  | trialityD4 q =>
    letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeTriality q H hH))
  | reeG2 m hm =>
    letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeReeGTwo m hm H hH))
  | reeF4 m hm =>
    letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := hsimple
    exact Or.inl (fun H hH => (by decide : 6≤32).trans (CFSGExceptionalThirtyTwoProperIndex.typeReeFFour m hm H hH))
  | tits => exact Or.inr (Or.inr trivial)
  | sporadic s => exact Or.inr (Or.inr trivial)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hk2 : 2≤D.factorCount) (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    MarkedC4.genRank G≤traceyPermutationGeneratorCeiling (Nat.card X) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple≃*j.Model) := by
  obtain ⟨j,⟨e⟩⟩ := hCFSG.classify D.Simple
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro h
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn with hp | hj
  · obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    obtain ⟨horder,houter⟩ := CFSGReduction.sufficientSimpleIndexBounds_of_mulEquiv e hp ell hell
    by_cases h32 : 32≤Nat.card X
    · exact Or.inl (PrimitiveSocleSmallMultipleStrictOrdinary.genRank_le_ceiling
        D ell hbelow hell hk2 horder h32 houter)
    · rcases model_index_six_or_pair_or_remaining j hn with hi | hpair | hj
      · have hell6 := SimpleModelMinimumIndexDegreeTransport.least_index_ge D e 6 ell hell hi
        have hell5 : 5≤ell := by omega
        have hd := primitiveSocle_power_le_degree hell5 horder (D.degreeForm hell)
        have hsq := (Nat.pow_le_pow_right (show 0<ell by omega) hk2).trans hd
        have h36 := Nat.pow_le_pow_left hell6 2
        norm_num at h36
        omega
      · exact Or.inl (PrimitiveSoclePairFamiliesCompleteOrdinary.genRank_le_ceiling D j hpair e hbelow)
      · exact Or.inr ⟨j,hj,⟨e⟩⟩
  · exact Or.inr ⟨j,hj,⟨e⟩⟩

theorem exists_generating_finset_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (hk2 : 2≤D.factorCount) (hbelow : SmallerTransitiveRankBound (Nat.card X)) :
    (∃ S : Finset G, Subgroup.closure (S : Set G)=⊤ ∧
      S.card≤traceyPermutationGeneratorCeiling (Nat.card X)) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple≃*j.Model) := by
  rcases genRank_le_ceiling_or_actual_remaining_model D hCFSG hk2 hbelow with h | h
  · obtain ⟨S,hcard,hS⟩ := MarkedC4.genRank_spec (G := G)
    exact Or.inl ⟨S,hS,hcard.le.trans h⟩
  · exact Or.inr h

end SymmetricSubgroupAsymptotics.PrimitiveMultifactorOrdinaryCFSGReduction
