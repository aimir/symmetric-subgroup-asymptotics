import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeDCompleteOneFactorOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelSharpPairAllDegreeOrdinary

/-! A displayed pair with the proved sufficient outer budget pays every
one-factor degree. The small sufficient-budget branch uses integral
prime multiplicity. In particular this removes the rank-four D cutoff
without replacing its actual sufficient bound by a sharp conjecture. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleSufficientPairAllDegreeOrdinary
open PrimitiveSocleRawStructure

theorem six_le_ceiling (n : ℕ) (hn : 12≤n) :
    6≤traceyPermutationGeneratorCeiling n := by
  by_cases hlarge : 32≤n
  · have hlog : 1≤Real.logb 2 (n:ℝ) := by
      have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
        (by norm_num : (0:ℝ)<2) (by exact_mod_cast (show 2≤n by omega) : (2:ℝ)≤n)
      simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using hh
    have hh := (UnitLogOrdinaryGeneratorTail.aggregate_le n hlarge).trans
      (Nat.le_ceil ((n:ℝ)/Real.sqrt (Real.logb 2 (n:ℝ))))
    change Real.logb 2 (n:ℝ)+5≤(traceyPermutationGeneratorCeiling n:ℝ) at hh
    have hc : (6:ℝ)≤(traceyPermutationGeneratorCeiling n:ℝ) := by linarith
    exact_mod_cast hc
  · change 6≤⌈(n:ℝ)/Real.sqrt (Real.logb 2 (n:ℝ))⌉₊
    apply IntegerLogSquareRootCeilingCertificate.le_ceil_of_square n 1 5 6
      (by omega) (by decide) (by decide)
    · simpa using (show n≤32 by omega)
    · nlinarith

theorem small_multiplicity_le (n ell out : ℕ) (hn : 5≤n) (hsmall : n<32)
    (hell : 0<ell) (helln : ell≤n) (hout : 0<out)
    (hbudget : SufficientOuterOrderBudget ell out) :
    2+ArithmeticFunction.cardFactors out≤traceyPermutationGeneratorCeiling n := by
  by_cases hsmallEll : ell<27
  · have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by exact_mod_cast hell : (0:ℝ)<ell)
      (by exact_mod_cast helln : (ell:ℝ)≤n)
    apply SmallSharpOuterPairNumerics.sharp_outer_small_multiplicity n out hn hsmall hout
    have hh := hbudget.log_three_of_small hsmallEll
    linarith
  · have hell32 : ell<32 := lt_of_le_of_lt helln hsmall
    have hl := Real.logb_lt_logb (by norm_num : (1:ℝ)<2)
      (by exact_mod_cast hell : (0:ℝ)<ell)
      (by exact_mod_cast hell32 : (ell:ℝ)<(2:ℝ)^5)
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at hl
    norm_num at hl
    have hb : out<2^(4+1) := by
      have ho := hbudget.log_six
      have hh : (out:ℝ)<32 := by linarith
      exact_mod_cast hh
    have hc := SmallSharpOuterPairNumerics.cardFactors_le_of_lt_pow out 4 hout hb
    exact (Nat.add_le_add_left hc 2).trans (six_le_ceiling n (by omega))

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) {M : Type} [Group M]

theorem genRank_le_ceiling (hk : D.factorCount=1) (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S:Set M)=⊤ ∧ S.card≤2)
    (hbudget : ∀ ell : ℕ, LeastProperIndex M ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer M))) :
    MarkedC4.genRank G≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  classical
  by_cases hn : 32≤Nat.card X
  · exact PrimitiveSocleModelPairOrdinaryTail.genRank_le_ceiling_of_outer_budget D hk e hpair hbudget hn
  obtain ⟨S,hS,hcard⟩ := hpair
  let U := S.image e.symm
  have hU : Subgroup.closure (U:Set D.Simple)=⊤ := by
    rw [Finset.coe_image]
    change Subgroup.closure (e.symm.toMonoidHom '' (S:Set M))=⊤
    rw [← MonoidHom.map_closure,hS]
    exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hUcard : U.card≤2 := Finset.card_image_le.trans hcard
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hell5 : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have helln := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact hbudget ell (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
  have hsmall := small_multiplicity_le (Nat.card X) ell (Nat.card (Outer D.Simple))
    (hell5.trans helln) (by omega) (by omega) helln (Nat.card_pos (α:=Outer D.Simple)) houter
  have hsimple : MarkedC4.genRank D.Simple≤2 := (MarkedC4.genRank_le hU).trans hUcard
  exact (PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk).trans
    ((Nat.add_le_add_right hsimple _).trans hsmall)

theorem exists_generating_finset (hk : D.factorCount=1) (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S:Set M)=⊤ ∧ S.card≤2)
    (hbudget : ∀ ell : ℕ, LeastProperIndex M ell →
      SufficientOuterOrderBudget ell (Nat.card (Outer M))) :
    ∃ U : Finset G, Subgroup.closure (U:Set G)=⊤ ∧
      U.card≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk e hpair hbudget)⟩

theorem typeD_genRank_le_ceiling (hk : D.factorCount=1)
    (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.D r q) :
    MarkedC4.genRank G≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  letI : IsSimpleGroup (CFSG.Models.D r q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.D r q) := Finite.of_equiv D.Simple e.toEquiv
  apply genRank_le_ceiling D hk e (CFSGReduction.typeD_twoGenerated_of_index r q hr)
  intro ell hell
  by_cases hfour : r=4
  · subst r
    exact (CFSGReduction.typeD_four_sufficientSimpleIndexBudget q ell hell).2
  · have hellT := CFSGReduction.leastProperIndex_of_mulEquiv e.symm ell hell
    have hell5 : 5≤ell := nonabelianSimple_leastProperIndex_five_le
      (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hellT.1
    exact SufficientOuterOrderBudget.of_sharp hell5
      (CFSGReduction.typeD_high_outer_card_le_log r (by omega) q ell hell)

theorem typeD_exists_generating_finset (hk : D.factorCount=1)
    (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.D r q) :
    ∃ U : Finset G, Subgroup.closure (U:Set G)=⊤ ∧
      U.card≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨U,hgen,hU.le.trans (typeD_genRank_le_ceiling D hk r hr q e)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleSufficientPairAllDegreeOrdinary
