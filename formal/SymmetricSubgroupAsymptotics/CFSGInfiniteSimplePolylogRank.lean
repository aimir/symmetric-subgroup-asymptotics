import SymmetricSubgroupAsymptotics.CFSGInfiniteRootSimplePolylogRank
import SymmetricSubgroupAsymptotics.CFSGInfiniteSylowSimplePolylogRank

/-! Actual simple ranks for every infinite CFSG family. The only residual
tags are the literal finite Tits/sporadic menu; no numerical callback occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInfiniteSimplePolylogRank
open PrimitiveSocleRawStructure CFSGReduction PrimitiveSimplePolylogRankTools
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

private theorem pair_rank {M : Type} [Group M]
    (e : D.Simple ≃* M) (hp : CFSGGeneration.TwoGenerated M)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ) ≤ 12*(Real.logb 2 (ell : ℝ))^2+1 := by
  have h2 : 2 ≤ ell := by
    obtain ⟨H,hH,he⟩ := hell.1
    have hh := H.one_lt_index_of_ne_top hH
    omega
  exact rank_le_of_pair (CFSGGeneration.of_mulEquiv e.symm hp) ell h2

theorem simple_rank_or_remaining (i : CFSG.Index) (e : D.Simple ≃* i.Model)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) :
    (MarkedC4.genRank D.Simple : ℝ) ≤ 12*(Real.logb 2 (ell : ℝ))^2+1 ∨
      RemainingModel i := by
  letI : Finite i.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup i.Model := e.symm.isSimpleGroup
  cases i with
  | cyclic p hp =>
    have hc : IsMulCommutative (CFSG.Index.cyclic p hp).Model := by
      change IsMulCommutative (Multiplicative (ZMod p))
      infer_instance
    exact (D.noncommutative ((isMulCommutative_congr e).mpr hc)).elim
  | alternating m hm =>
    left
    apply pair_rank D e ?_ ell hell
    obtain ⟨a,ha⟩ := CFSGAlternatingGeneration.exists_generating_tuple m hm
    exact CFSGGeneration.of_generating_family a ha (by simp)
  | A r q hr hs =>
    exact Or.inl (pair_rank D e (typeA_twoGenerated r q hr hs) ell hell)
  | B r q hr =>
    letI : IsSimpleGroup (CFSG.Models.B r q) := e.symm.isSimpleGroup
    exact Or.inl (pair_rank D e (typeB_twoGenerated_of_index r q hr) ell hell)
  | C r q hr hs =>
    letI : IsSimpleGroup (CFSG.Models.C r q) := e.symm.isSimpleGroup
    exact Or.inl (pair_rank D e (typeC_twoGenerated_of_index r q hr hs) ell hell)
  | D r q hr =>
    letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
    exact Or.inl (pair_rank D e (typeD_twoGenerated_of_index r q hr) ell hell)
  | E6 q =>
    exact Or.inl (CFSGInfiniteRootSimplePolylogRank.typeE6_simple_rank D q e ell hell)
  | E7 q =>
    exact Or.inl (CFSGInfiniteRootSimplePolylogRank.typeE7_simple_rank D q e ell hell)
  | E8 q =>
    exact Or.inl (CFSGInfiniteRootSimplePolylogRank.typeE8_simple_rank D q e ell hell)
  | F4 q =>
    exact Or.inl (CFSGInfiniteSylowSimplePolylogRank.FFour.simple_rank D q e ell hell)
  | G2 q hs =>
    exact Or.inl (CFSGInfiniteSylowSimplePolylogRank.GTwo.simple_rank D q hs e ell hell)
  | twistedA r q hr hs =>
    exact Or.inl (CFSGInfiniteSylowSimplePolylogRank.Unitary.simple_rank D r q hr hs e ell hell)
  | twistedD r q hr =>
    exact Or.inl (CFSGInfiniteRootSimplePolylogRank.twistedD_simple_rank D r hr q e ell hell)
  | twistedE6 q =>
    exact Or.inl (CFSGInfiniteSylowSimplePolylogRank.TwistedESix.simple_rank D q e ell hell)
  | trialityD4 q =>
    exact Or.inl (CFSGInfiniteSylowSimplePolylogRank.Triality.simple_rank D q e ell hell)
  | suzuki m hm =>
    exact Or.inl (pair_rank D e (CFSGSuzukiGeneration.suzuki_twoGenerated m hm) ell hell)
  | reeG2 m hm =>
    exact Or.inl (CFSGInfiniteSylowSimplePolylogRank.ReeGTwo.simple_rank D m hm e ell hell)
  | reeF4 m hm =>
    exact Or.inl (CFSGInfiniteSylowSimplePolylogRank.ReeFFour.simple_rank D m (by omega) e ell hell)
  | tits => exact Or.inr trivial
  | sporadic s => exact Or.inr trivial

variable [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

theorem primitive_rank_or_actual_finite_model (hCFSG : CFSG.CFSGClassification) :
    (MarkedC4.genRank G : ℝ) ≤ 25*(Real.logb 2 (Nat.card X : ℝ))^2+
      4*Real.logb 2 (Nat.card X : ℝ)+2 ∨
      ∃ i : CFSG.Index, RemainingModel i ∧ Nonempty (D.Simple ≃* i.Model) := by
  obtain ⟨i,⟨e⟩⟩ := hCFSG.classify D.Simple
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  rcases simple_rank_or_remaining D i e ell hell with hr | hi
  · letI : Finite i.Model := Finite.of_equiv D.Simple e.toEquiv
    letI : IsSimpleGroup i.Model := e.symm.isSimpleGroup
    have hn : ¬ IsMulCommutative i.Model := by
      intro h
      exact D.noncommutative ((isMulCommutative_congr e).mpr h)
    rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining i hn with hb | hi
    · obtain ⟨ho,ha⟩ := sufficientSimpleIndexBounds_of_mulEquiv e hb ell hell
      exact Or.inl (primitive_rank_le_of_simple_packet D ell hell ho ha hr)
    · exact Or.inr ⟨i,hi,⟨e⟩⟩
  · exact Or.inr ⟨i,hi,⟨e⟩⟩

end SymmetricSubgroupAsymptotics.CFSGInfiniteSimplePolylogRank
