import SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryTail
import SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseBoundedParameters
import SymmetricSubgroupAsymptotics.PrimitiveAffinePrimeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineFourOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics

/-! The actual primitive-affine coarse branch, with only degrees16 and32
left explicit. The argument shares one complement-order certificate over
all bounded parameter pairs and the uniform large-degree tail. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryFrontier

theorem two_le_ceiling (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ traceyPermutationGeneratorCeiling n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) (by linarith)
  have hs : 0 < Real.sqrt (Real.logb 2 (n : ℝ)) := Real.sqrt_pos.mpr hL
  have hlog := CFSGCoarsePrimitiveNumerics.logb_nat_le_nat n
  have hsq := Real.sq_sqrt hL.le
  have hlt : Real.sqrt (Real.logb 2 (n : ℝ)) < n := by nlinarith only [hnR,hlog,hsq]
  have hr : (1 : ℝ) < (n : ℝ) / Real.sqrt (Real.logb 2 (n : ℝ)) :=
    (lt_div_iff₀ hs).mpr (by simpa only [one_mul] using hlt)
  apply Nat.add_one_le_ceil_iff.mpr
  simpa only [Nat.cast_one] using hr

theorem genRank_le_ceiling_except_sixteen_thirtyTwo
    (n : ℕ) (hn : 2 ≤ n) (J : Subgroup (Equiv.Perm (Fin n)))
    (P : PrimitiveAffineProfile J (Fin n))
    (hprimitive : MulAction.IsPreprimitive J (Fin n))
    (h16 : n ≠ 16) (h32 : n ≠ 32) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1<n by omega))
  by_cases htail : 1024 ≤ n
  · simpa only [Nat.card_fin] using PrimitiveAffineCoarseOrdinaryTail.genRank_le_ceiling
      P hprimitive (by simpa only [Nat.card_fin] using htail)
  by_cases hprime : n.Prime
  · exact (PrimitiveAffinePrimeOrdinaryGenerators.genRank_le_two P hprimitive hprime).trans
      (two_le_ceiling n hn)
  by_cases hfour : n=4
  · subst n
    exact (PrimitiveAffineFourOrdinaryGenerators.genRank_le_two P hprimitive).trans
      (two_le_ceiling 4 (by decide))
  by_cases height : n=8
  · subst n
    have hr := P.subnormal_genRank_le_three_of_degreeEight hprimitive
      (0 : Fin 8) (by simp) ⊤ (by exact Subgroup.Normal.isSubnormal inferInstance)
    have he := CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J)
    rw [he] at hr
    exact hr.trans (IntegerLogSquareRootCeilingCertificate.le_ceil_of_square
      8 1 3 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hdegree : n=P.p^C.d := by
    simpa only [Nat.card_fin,PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (⟨0,by omega⟩ : Fin n)
  have hd2 : 2 ≤ C.d := by
    have hdpos := C.d_pos
    by_contra h
    have hd1 : C.d=1 := by omega
    apply hprime
    simpa only [hdegree,hd1,pow_one] using P.p_prime
  have hbinary : P.p=2 → 6≤C.d := by
    intro hp
    by_contra h
    have hcases : C.d=2 ∨ C.d=3 ∨ C.d=4 ∨ C.d=5 := by omega
    rcases hcases with hd | hd | hd | hd
    · apply hfour
      simpa only [hp,hd] using hdegree
    · apply height
      simpa only [hp,hd] using hdegree
    · apply h16
      simpa only [hp,hd] using hdegree
    · apply h32
      simpa only [hp,hd] using hdegree
  simpa only [Nat.card_fin] using
    PrimitiveAffineCoarseBoundedParameters.genRank_le_ceiling P hprimitive C hd2
      (by rw [←hdegree]; omega) hbinary

end SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseOrdinaryFrontier
