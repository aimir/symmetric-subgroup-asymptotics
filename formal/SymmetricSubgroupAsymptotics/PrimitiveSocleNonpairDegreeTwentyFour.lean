import SymmetricSubgroupAsymptotics.PrimitiveSocleNonpairDegreeEight
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoCoupledIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeCoupledIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryHigherCoupledIndex

/-! Existing SAME-stabilizer coupled-index bounds exclude EVERY admissible
unitary model below degree24, including PSU_5(2). Together with actual
twisted-D and exceptional indices, every nonpaired Lie factor is excluded
in that whole degree range. Classification leaves only actual paired-model
or Tits/sporadic factor witnesses. No generator theorem, model-order table,
new torus argument or bounded action catalogue occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleNonpairDegreeTwentyFour
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)
open CFSGTwistedAUnitaryCoordinates

private theorem rank_two_proper_index (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.TwistedA 2 q)]
    (H : Subgroup (CFSG.Models.TwistedA 2 q)) (hH : H ≠ ⊤) : 24 ≤ H.index := by
  by_cases hlarge : 5 ≤ q.order
  · have hb : 25 ≤ q.order^2 := Nat.pow_le_pow_left hlarge 2
    have hi := twistedA_admissible_field_power_le_proper_index 2 (by decide) q
      (by intro _; omega) H hH
    omega
  have hgcd : (q.order+1).gcd 3 = 1 := by
    have hc : q.order = 3 ∨ q.order = 4 := by omega
    rcases hc with h | h <;> norm_num [h]
  have hp : 2 ≤ q.prime := q.prime_isPrime.two_le
  have hp2 : 4 ≤ q.prime^2 := Nat.pow_le_pow_left hp 2
  rcases twistedA_rankTwo_coupled_proper_index q hq H hH with h | h | h
  · have hb : 27 ≤ q.order^3 := Nat.pow_le_pow_left hq 3
    omega
  · have hb : 24 ≤ q.prime^2*q.order*(q.order-1) := by
      calc
        24 = 4*3*2 := by decide
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hp2 hq) (by omega)
    exact hb.trans h
  · rw [hgcd,one_mul] at h
    have hb : 24 ≤ q.prime*q.order*(q.order+1) := by
      calc
        24 = 2*3*4 := by decide
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hp hq) (by omega)
    exact hb.trans h

theorem unitary_proper_index (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hs : r = 2 → q.order ≠ 2) [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H ≠ ⊤) : 24 ≤ H.index := by
  have hq := CFSGTwistedAQuadraticTrace.order_two_le q
  by_cases htwo : r = 2
  · subst r
    exact rank_two_proper_index q (by have hh := hs rfl; omega) H hH
  by_cases hthree : r = 3
  · subst r
    by_cases hb : q.order = 2
    · exact twistedA_rankThree_binary_coupled_proper_index q hb H hH
    · have hq3 : 3 ≤ q.order := by omega
      have hp : 27 ≤ q.order^3 := Nat.pow_le_pow_left hq3 3
      have hi := twistedA_admissible_field_power_le_proper_index 3 (by decide) q
        (by omega) H hH
      omega
  have hr4 : 4 ≤ r := by omega
  have he : 3 ≤ 2*r-5 := by omega
  have hleft : 3 ≤ q.order^2-1 := by
    have hh : 4 ≤ q.order^2 := Nat.pow_le_pow_left hq 2
    omega
  have hright : 8 ≤ q.order^(2*r-5) := (Nat.pow_le_pow_left hq 3).trans
    (Nat.pow_le_pow_right (by omega : 0 < q.order) he)
  have hb : 48 ≤ q.prime*(q.order^2-1)*q.order^(2*r-5) := by
    calc
      48 = 2*3*8 := by decide
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul q.prime_isPrime.two_le hleft) hright
  exact (by decide : 24 ≤ 48).trans
    (hb.trans (twistedA_higher_coupled_proper_index r hr4 q H hH))

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem unitary_degree_ge_twenty_four (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hs : r = 2 → q.order ≠ 2) (e : D.Simple ≃* CFSG.Models.TwistedA r q) :
    24 ≤ Nat.card X := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  exact SimpleModelMinimumIndexDegreeTransport.degree_ge D e 24 (unitary_proper_index r hr q hs)

theorem degree_ge_twenty_four_of_nonpair (j : CFSG.Index) (e : D.Simple ≃* j.Model)
    (hpair : ¬ PairFamily j) (hremaining : ¬ RemainingModel j) : 24 ≤ Nat.card X := by
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
  | twistedA r q hr hs => exact unitary_degree_ge_twenty_four D r hr q hs e
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
      exact SimpleModelMinimumIndexDegreeTransport.degree_ge D e 24
        (fun H hH => hprod.trans
          (CFSGReduction.typeTwistedD_point_radical_le_proper_index r hr q H hH))
  | F4 q =>
      letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeFFour q))
  | G2 q hs =>
      letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeGTwo q hs))
  | E6 q =>
      letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeESix q))
  | E7 q =>
      letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeESeven q))
  | E8 q =>
      letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeEEight q))
  | twistedE6 q =>
      letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeTwistedESix q))
  | trialityD4 q =>
      letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeTriality q))
  | reeG2 m hm =>
      letI : IsSimpleGroup (CFSG.Models.ReeG2 m) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeReeGTwo m hm))
  | reeF4 m hm =>
      letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
      exact (by decide : 24 ≤ 32).trans (SimpleModelMinimumIndexDegreeTransport.degree_ge D e 32
        (CFSGExceptionalThirtyTwoProperIndex.typeReeFFour m hm))
  | tits => exact (hremaining trivial).elim
  | sporadic s => exact (hremaining trivial).elim

theorem pair_family_or_actual_remaining_of_degree_below_twenty_four
    (hCFSG : CFSG.CFSGClassification) (hsmall : Nat.card X < 24) :
    (∃ j : CFSG.Index, PairFamily j ∧ Nonempty (D.Simple ≃* j.Model)) ∨
      ∃ j : CFSG.Index, RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  obtain ⟨j,⟨e⟩⟩ := hCFSG.classify D.Simple
  by_cases hp : PairFamily j
  · exact Or.inl ⟨j,hp,⟨e⟩⟩
  by_cases hr : RemainingModel j
  · exact Or.inr ⟨j,hr,⟨e⟩⟩
  have hh := degree_ge_twenty_four_of_nonpair D j e hp hr
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleNonpairDegreeTwentyFour
