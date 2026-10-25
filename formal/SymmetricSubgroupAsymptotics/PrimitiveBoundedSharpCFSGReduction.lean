import SymmetricSubgroupAsymptotics.PrimitiveSocleSixToTenSharpCFSGReduction
import SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineNineOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators
import SymmetricSubgroupAsymptotics.SmallFourPointOrdinaryGenerators

/-! The ORIGINAL primitive sharp ordinary-generator reduction throughout
4..21. Every actual affine profile is paid except degree16, using its
literal prime-power degree and actual complement/translation generators.
Every nonaffine Lie factor is paid by the checked small-index/head/outer
arguments. The only residuals are an actual affine profile at16 or actual
Tits/sporadic factor data. No induction, current-degree Tracey/MN bound,
primitive action catalogue, or new model callback is assumed. The
imprimitive affine sharp problem is separate from this theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpCFSGReduction
open PrimitiveSocleRawStructure TraceySharpHalfDegreeNumerics
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

theorem two_le_sharpFloor_four : 2 ≤ sharpFloor 4 :=
  TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square 4 2 2 (by decide)
    (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 4 2 (by decide) (by decide)) (by decide)

/-- Pure prime-power arithmetic, not a classification of group actions. -/
theorem prime_power_band (p d n : ℕ) (hp : p.Prime) (heq : n = p^d)
    (hlo : 4 ≤ n) (hhi : n ≤ 21) :
    n.Prime ∨ n = 4 ∨ n = 8 ∨ n = 9 ∨ n = 16 := by
  have hdpos : 1 ≤ d := by
    by_contra hh
    have hd0 : d = 0 := by omega
    rw [hd0,pow_zero] at heq
    omega
  by_cases hd1 : d = 1
  · exact Or.inl (by simpa only [heq,hd1,pow_one] using hp)
  have hd2 : 2 ≤ d := by omega
  have hp5 : p < 5 := by
    by_contra hh
    have hb := (Nat.pow_le_pow_left (show 5 ≤ p by omega) 2).trans
      (Nat.pow_le_pow_right hp.pos hd2)
    rw [← heq] at hb
    norm_num at hb
    omega
  have hcases : p = 2 ∨ p = 3 := by
    have hp2 := hp.two_le
    have hp4 : p ≠ 4 := by intro h; rw [h] at hp; norm_num at hp
    omega
  rcases hcases with rfl | rfl
  · have hdle : d ≤ 4 := by
      by_contra hh
      have hb : 32 ≤ 2^d := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ d)
      rw [← heq] at hb
      omega
    have hc : d = 2 ∨ d = 3 ∨ d = 4 := by omega
    rcases hc with h | h | h
    · exact Or.inr (Or.inl (by simpa only [h] using heq))
    · exact Or.inr (Or.inr (Or.inl (by simpa only [h] using heq)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [h] using heq))))
  · have hdle : d ≤ 2 := by
      by_contra hh
      have hb : 27 ≤ 3^d := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 3 ≤ d)
      rw [← heq] at hb
      omega
    have hd : d = 2 := by omega
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hd] using heq))))

private theorem two_le_sharpFloor_of_band (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21) :
    2 ≤ sharpFloor n := by
  by_cases h4 : n = 4
  · subst n
    exact two_le_sharpFloor_four
  by_cases h5 : n = 5
  · subst n
    exact NaturalDegreeFiveSocleOrdinaryGenerators.two_le_sharpFloor_five
  by_cases hsmall : n ≤ 10
  · have hh := PrimitiveSocleSixToTenSharpCFSGReduction.smallRank_le_sharpFloor
      n (by omega) hsmall
    have htwo : 2 ≤ if n ≤ 7 then 3 else 4 := by split_ifs <;> decide
    exact htwo.trans hh
  · exact (by decide : 2 ≤ 5).trans
      (PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.five_le_sharpFloor_of_band
        n (by omega) hhi)

theorem genRank_le_sharpFloor_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    MarkedC4.genRank J ≤ sharpFloor n ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  by_cases hlarge : 11 ≤ n
  · exact PrimitiveBoundedSharpElevenToTwentyOneCFSGReduction.genRank_le_sharpFloor_or_actual_residual
      hCFSG n hlarge hhi J hprimitive
  have hsmall : n ≤ 10 := by omega
  by_cases h4 : n = 4
  · subst n
    exact Or.inl ((SmallFourPointOrdinaryGenerators.subgroup_genRank_le_two J).trans
      two_le_sharpFloor_four)
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1 < n by omega))
  letI : MulAction.IsPreprimitive J (Fin n) := hprimitive
  obtain ⟨P⟩ := publishedONanScottStructure J (Fin n)
  cases P with
  | inr P =>
      obtain ⟨d,hd⟩ := P.degree_eq_prime_power (⟨0,by omega⟩ : Fin n)
      rcases prime_power_band P.p d n P.p_prime hd hlo hhi with hp | hfour | h8 | h9 | h16
      · exact Or.inl ((PrimitiveAffinePrimeOrdinaryGenerators.genRank_le_two P hprimitive hp).trans
          (two_le_sharpFloor_of_band n hlo hhi))
      · exact (h4 hfour).elim
      · subst n
        have hr := P.subnormal_genRank_le_three_of_degreeEight hprimitive (0 : Fin 8)
          (by simp only [Nat.card_fin]) ⊤ (by exact Subgroup.Normal.isSubnormal inferInstance)
        have he := CoprimeNilpotentProductGenerators.genRank_mulEquiv
          (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J)
        rw [he] at hr
        have hf : 3 ≤ sharpFloor 8 :=
          TinyPrimeTopSharpFloorNumerics.le_sharpFloor_of_square 8 3 3 (by decide)
            (TinyPrimeTopSharpFloorNumerics.log_le_of_pow 8 3 (by decide) (by decide)) (by decide)
        exact Or.inl (hr.trans hf)
      · subst n
        have hg := PrimitiveAffineNineOrdinaryGenerators.genRank_le_sharpFloor P hprimitive
          (by simp only [Nat.card_fin])
        exact Or.inl (by simpa only [Nat.card_fin] using hg)
      · omega
  | inl D =>
      by_cases h5 : n = 5
      · subst n
        rcases NaturalDegreeFiveSocleOrdinaryGenerators.genRank_le_sharpFloor_or_actual_remaining_model
          J D hCFSG with hg | ⟨j,hj,e⟩
        · exact Or.inl hg
        · exact Or.inr (Or.inr ⟨D,j,hj,e⟩)
      · have hlow : 6 ≤ Nat.card (Fin n) := by simpa only [Nat.card_fin] using (show 6 ≤ n by omega)
        have hhigh : Nat.card (Fin n) ≤ 10 := by simpa only [Nat.card_fin] using hsmall
        rcases PrimitiveSocleSixToTenSharpCFSGReduction.genRank_le_sharpFloor_or_actual_remaining_model
          D hCFSG hlow hhigh with hg | ⟨j,hj,e⟩
        · exact Or.inl (by simpa only [Nat.card_fin] using hg)
        · exact Or.inr (Or.inr ⟨D,j,hj,e⟩)

theorem exists_generating_finset_or_actual_residual
    (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 21)
    (J : Subgroup (Equiv.Perm (Fin n))) (hprimitive : MulAction.IsPreprimitive J (Fin n)) :
    (∃ F : Finset J, Subgroup.closure (F : Set J) = ⊤ ∧ F.card ≤ sharpFloor n) ∨
      (n = 16 ∧ Nonempty (PrimitiveAffineProfile J (Fin n))) ∨
      ∃ D : NonaffineData J (Fin n), ∃ j : CFSG.Index,
        RemainingModel j ∧ Nonempty (D.Simple ≃* j.Model) := by
  rcases genRank_le_sharpFloor_or_actual_residual hCFSG n hlo hhi J hprimitive with hg | hr
  · obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := J)
    exact Or.inl ⟨F,hgen,hcard.le.trans hg⟩
  · exact Or.inr hr

end SymmetricSubgroupAsymptotics.PrimitiveBoundedSharpCFSGReduction
