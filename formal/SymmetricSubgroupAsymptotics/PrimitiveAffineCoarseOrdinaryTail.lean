import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.PrimitiveProductOrdinaryRealTail
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput

/-! The coarse primitive-affine tail from the actual complement's linear
order. No smaller-degree induction, soluble-complement restriction or
global permutation-generator bound is a premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryTail

variable {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P

theorem genRank_le_log_square_add_one
    (hprimitive : MulAction.IsPreprimitive G X) :
    (MarkedC4.genRank G : ℝ) ≤ (Real.logb 2 (Nat.card X : ℝ)) ^ 2 + 1 := by
  let x : X := Classical.arbitrary X
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  let L := Real.logb 2 (Nat.card X : ℝ)
  have hn : 2 ≤ Nat.card X := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hL : 1 ≤ L := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ Nat.card X by exact_mod_cast hn)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hdegree : Nat.card X = P.p ^ C.d := by
    simpa only [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv x
  have hd : (C.d : ℝ) ≤ L := by
    have hh : (2 : ℕ) ^ C.d ≤ Nat.card X := by
      rw [hdegree]
      exact Nat.pow_le_pow_left P.p_prime.two_le C.d
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (pow_pos (by norm_num : (0 : ℝ) < 2) C.d)
      (show (2 : ℝ) ^ C.d ≤ Nat.card X by exact_mod_cast hh)
    simpa only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using hlog
  have hcard : (2 : ℕ) ^ MarkedC4.genRank (P.complement x) ≤
      Nat.card X ^ C.d :=
    (FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card (P.complement x)).trans
      (P.complement_card_le_degree_pow_finrank C.equiv x)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) (MarkedC4.genRank (P.complement x)))
    (show (2 : ℝ) ^ MarkedC4.genRank (P.complement x) ≤
      (Nat.card X : ℝ) ^ C.d by exact_mod_cast hcard)
  have hcomp : (MarkedC4.genRank (P.complement x) : ℝ) ≤ (C.d : ℝ) * L := by
    simpa only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using hlog
  have hrank : (MarkedC4.genRank G : ℝ) ≤
      (MarkedC4.genRank (P.complement x) : ℝ) + 1 := by
    exact_mod_cast P.genRank_le_complement_add_one hprimitive x
  change (MarkedC4.genRank G : ℝ) ≤ L ^ 2 + 1
  nlinarith only [hrank, hcomp, mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ L)]

theorem genRank_le_ceiling
    (hprimitive : MulAction.IsPreprimitive G X) (hn : 1024 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hL : 1 ≤ Real.logb 2 (Nat.card X : ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ Nat.card X by exact_mod_cast (show 2 ≤ Nat.card X by omega))
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hh
  have hcost := genRank_le_log_square_add_one P hprimitive
  have htail := PrimitiveProductOrdinaryRealTail.aggregate_le (Nat.card X) hn
  have hreal : (MarkedC4.genRank G : ℝ) ≤
      (Nat.card X : ℝ) / Real.sqrt (Real.logb 2 (Nat.card X : ℝ)) := by
    nlinarith only [hcost, htail, Real.sqrt_nonneg (Nat.card X : ℝ), hL]
  have hh := hreal.trans
    (Nat.le_ceil ((Nat.card X : ℝ) / Real.sqrt (Real.logb 2 (Nat.card X : ℝ))))
  change (MarkedC4.genRank G : ℝ) ≤
    (traceyPermutationGeneratorCeiling (Nat.card X) : ℝ) at hh
  exact_mod_cast hh

theorem exists_generating_finset
    (hprimitive : MulAction.IsPreprimitive G X) (hn : 1024 ≤ Nat.card X) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
      S.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨S, hS, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨S, hgen, hS.le.trans (genRank_le_ceiling P hprimitive hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryTail
