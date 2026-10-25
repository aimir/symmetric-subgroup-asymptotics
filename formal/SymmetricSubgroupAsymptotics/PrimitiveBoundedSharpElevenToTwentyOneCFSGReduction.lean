import SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeOrdinaryGenerators
import Mathlib.Tactic.IntervalCases

/-! Original primitive sharp ordinary generation in the whole degree
band11..21. Nonaffine paired models pay rank2+actual outer multiplicity3.
Every other Lie model is excluded by the proved actual index>=24. Affine
degrees in this band are prime or16, proved from the literal prime-power
degree; prime degrees use their actual cyclic complement. The only
residuals are an actual affine profile at16 or actual Tits/sporadic factor
data. No induction, published Tracey/MN, or finite catalogue is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction
open OriginalNonaffinePairFamiliesBlockOrdinaryStep (PairFamily)

theorem five_le_sharpFloor_of_band (n : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 21) :
    5 ≤ sharpFloor n := by
  by_cases h11 : n = 11
  · subst n
    have hp : (11 : ℝ)^2 ≤ (2 : ℝ)^7 := by norm_num
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < (11 : ℝ)^2) hp
    simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have hroot : Real.sqrt (Real.logb 2 (11 : ℝ)) ≤ 15/8 :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith only [hl]⟩
    have hthree : (12/7 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
    have hpos : 0 < Real.logb 2 (11 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
    apply Nat.le_floor
    apply (le_div_iff₀ (show 0 < 2*Real.sqrt (Real.logb 2 (11 : ℝ)) by positivity)).mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hroot,hthree]
  by_cases hb : n ≤ 16
  · exact TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square n 5 4 (by omega)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow n 4 (by omega) (by simpa using hb))
      (by have hh := Nat.pow_le_pow_left (show 12 ≤ n by omega) 2; norm_num at hh ⊢; omega)
  · exact TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square n 5 5 (by omega)
      (TinyPrimeTopSharpFloorNumerics.log_le_of_pow n 5 (by omega) (by norm_num; omega))
      (by have hh := Nat.pow_le_pow_left (show 17 ≤ n by omega) 2; norm_num at hh ⊢; omega)

private theorem prime_of_prime_power_band (p d n : ℕ) (hp : p.Prime)
    (heq : n = p^d) (hlo : 11 ≤ n) (hhi : n ≤ 21) (h16 : n ≠ 16) : n.Prime := by
  have hdpos : 1 ≤ d := by
    by_contra hh
    have hd0 : d = 0 := by omega
    rw [hd0,pow_zero] at heq
    omega
  by_cases hd1 : d = 1
  · simpa only [heq,hd1,pow_one] using hp
  have hd2 : 2 ≤ d := by omega
  have hp5 : p < 5 := by
    by_contra hh
    have hpow : 25 ≤ p^d := (Nat.pow_le_pow_left (show 5 ≤ p by omega) 2).trans
      (Nat.pow_le_pow_right hp.pos hd2)
    rw [← heq] at hpow
    omega
  have hcases : p = 2 ∨ p = 3 := by
    have hp2 := hp.two_le
    have hp4 : p ≠ 4 := by
      intro he
      have hh := hp
      rw [he] at hh
      norm_num at hh
    omega
  rcases hcases with rfl | rfl
  · have hdle : d ≤ 4 := by
      by_contra hh
      have hpow : 32 ≤ 2^d := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ d by omega)
      rw [← heq] at hpow
      omega
    have hdge : 4 ≤ d := by
      by_contra hh
      have hpow : 2^d ≤ 8 := Nat.pow_le_pow_right (by decide : 0 < 2) (show d ≤ 3 by omega)
      rw [← heq] at hpow
      omega
    have hd : d = 4 := by omega
    exact (h16 (by simpa only [hd] using heq)).elim
  · have hdle : d ≤ 2 := by
      by_contra hh
      have hpow : 27 ≤ 3^d := Nat.pow_le_pow_right (by decide : 0 < 3) (show 3 ≤ d by omega)
      rw [← heq] at hpow
      omega
    have hd : d = 2 := by omega
    rw [hd] at heq
    norm_num at heq
    omega

section Nonaffine
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_five_of_actual_pair_packet (hsmall : Nat.card X < 25)
    (S : Finset D.Simple) (hS : Subgroup.closure (S : Set D.Simple) = ⊤) (hcard : S.card ≤ 2)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) (horder : ell^2 < Nat.card D.Simple)
    (houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple))) :
    MarkedC4.genRank G ≤ 5 := by
  obtain ⟨hk,hout⟩ := PrimitiveSocleDegreeBelowTwentyFiveOuterMultiplicity.factor_and_outer_multiplicity
    D hsmall ell hell horder houter
  have hs : MarkedC4.genRank D.Simple ≤ 2 := (MarkedC4.genRank_le hS).trans hcard
  have hg := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  omega

theorem genRank_le_sharpFloor_of_pair_family (j : CFSG.Index) (hj : PairFamily j)
    (e : D.Simple ≃* j.Model) (hlo : 11 ≤ Nat.card X) (hhi : Nat.card X ≤ 21) :
    MarkedC4.genRank G ≤ sharpFloor (Nat.card X) := by
  classical
  letI : Finite j.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup j.Model := e.symm.isSimpleGroup
  have hn : ¬ IsMulCommutative j.Model := by
    intro hh
    exact D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr hh)
  rcases CFSGSimpleIndexPacketOrTitsSporadic.model_packet_or_remaining j hn with hp | hr
  · obtain ⟨S,hS,hcard⟩ := OriginalNonaffineSmallPairFamiliesBlockOrdinaryStep.model_pair_of_family j hj
    let U := S.image e.symm
    have hU : Subgroup.closure (U : Set D.Simple) = ⊤ := by
      rw [Finset.coe_image]
      change Subgroup.closure (e.symm.toMonoidHom '' (S : Set j.Model)) = ⊤
      rw [← MonoidHom.map_closure,hS]
      exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
    have hUcard : U.card ≤ 2 := Finset.card_image_le.trans hcard
    obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hm := hp ell (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
    have horder : ell^2 < Nat.card D.Simple := by simpa only [Nat.card_congr e.toEquiv] using hm.1
    have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
      rw [CFSGReduction.outer_card_congr e]
      exact hm.2
    exact (genRank_le_five_of_actual_pair_packet D (by omega) U hU hUcard ell hell horder houter).trans
      (five_le_sharpFloor_of_band (Nat.card X) hlo hhi)
  · have hnot : ¬ RemainingModel j := by
      cases j <;> simp_all only [PairFamily,RemainingModel]
    exact (hnot hr).elim
end Nonaffine

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
  obtain ⟨P⟩ := publishedONanScottStructure J (Fin n)
  cases P with
  | inr P =>
      by_cases h16 : n = 16
      · exact Or.inr (Or.inl ⟨h16,⟨P⟩⟩)
      obtain ⟨d,hd⟩ := P.degree_eq_prime_power (⟨0,by omega⟩ : Fin n)
      have hp := prime_of_prime_power_band P.p d n P.p_prime hd hlo hhi h16
      have hg := PrimitiveAffinePrimeOrdinaryGenerators.genRank_le_two P hprimitive hp
      exact Or.inl (hg.trans ((by decide : 2 ≤ 5).trans (five_le_sharpFloor_of_band n hlo hhi)))
  | inl D =>
      rcases PrimitiveSocleNonpairDegreeTwentyFour.pair_family_or_actual_remaining_of_degree_below_twenty_four
        D hCFSG (by simpa only [Nat.card_fin] using (show n < 24 by omega)) with ⟨j,hj,⟨e⟩⟩ | hm
      · have hlow : 11 ≤ Nat.card (Fin n) := by simpa only [Nat.card_fin] using hlo
        have hhigh : Nat.card (Fin n) ≤ 21 := by simpa only [Nat.card_fin] using hhi
        have hg := genRank_le_sharpFloor_of_pair_family D j hj e hlow hhigh
        exact Or.inl (by simpa only [Nat.card_fin] using hg)
      · obtain ⟨j,hj,e⟩ := hm
        exact Or.inr (Or.inr ⟨D,j,hj,e⟩)

theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hlo : 11 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧ F.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_sharpFloor_or_actual_residual hCFSG n hlo hhi J hprimitive with hg | hr
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hcard.le.trans hg⟩
  · exact Or.inr hr

end SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction
