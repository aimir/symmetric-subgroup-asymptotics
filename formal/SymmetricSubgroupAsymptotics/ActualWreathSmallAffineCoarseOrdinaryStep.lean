import SymmetricSubgroupAsymptotics.ActualWreathBoundedMultiplicityJointCost
import SymmetricSubgroupAsymptotics.SmallAffineJointLargePrimaryNumerics
import SymmetricSubgroupAsymptotics.SmallAffineJointTinyMoreCertificates

/-! Independent coarse ordinary generation for correlated states whose
literal local orders divide20,42,432, at local point degrees5,7,9.
The same chief cost is used in every characteristic and prime regime.
Only the actual top ceiling is assumed; no global permutation theorem,
affine recognition, or fitted scalar inequality is a hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathSmallAffineCoarseOrdinaryStep
open ActualWreathOrdinaryChiefRecurrence SmallAffineJointTinyCertificates

/-- Literal local-order bounds, justified separately on the original profiles. -/
def orderBound (r : ℕ) : ℕ := if r = 5 then 20 else if r = 7 then 42 else 432
private def totalMultiplicity (r : ℕ) : ℕ := if r = 9 then 7 else 3
private def maxMultiplicity (r : ℕ) : ℕ := if r = 5 then 2 else if r = 7 then 1 else 4
private def shiftBound (r : ℕ) : ℝ := if r = 5 then 7/3 else if r = 7 then 3 else 10/3

private theorem factorization_bound (N m : ℕ)
    (h : ∀ p ∈ N.factorization.support, N.factorization p ≤ m) :
    ∀ p, N.factorization p ≤ m := by
  intro p
  by_cases hp : p ∈ N.factorization.support
  · exact h p hp
  · have hz : N.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    rw [hz]
    exact Nat.zero_le _

private theorem arithmetic_data (r : ℕ) (hr : r = 5 ∨ r = 7 ∨ r = 9) :
    orderBound r ≠ 0 ∧ ArithmeticFunction.cardFactors (orderBound r) ≤ totalMultiplicity r ∧
      (∀ p, (orderBound r).factorization p ≤ maxMultiplicity r) ∧
        maxMultiplicity r ≤ totalMultiplicity r := by
  rcases hr with rfl | rfl | rfl
  all_goals refine ⟨by decide,by decide +kernel,?_,by decide⟩
  all_goals exact factorization_bound _ _ (by decide +kernel)

private theorem log_shift (r : ℕ) (hr : r = 5 ∨ r = 7 ∨ r = 9) :
    Real.logb 2 (r : ℝ) ≤ shiftBound r := by
  rcases hr with rfl | rfl | rfl
  · have hh := IntegerLogSquareRootCeilingCertificate.log_upper 5 3 7
      (by decide) (by decide) (by decide)
    simpa [shiftBound] using hh
  · have hh := IntegerLogSquareRootCeilingCertificate.log_upper 7 1 3
      (by decide) (by decide) (by decide)
    simpa [shiftBound] using hh
  · have hh := IntegerLogSquareRootCeilingCertificate.log_upper 9 3 10
      (by decide) (by decide) (by decide)
    simpa [shiftBound] using hh

private theorem large_aggregate (r : ℕ) (hr : r = 5 ∨ r = 7 ∨ r = 9)
    (t : ℕ) (ht : 8 ≤ t) (g : ℝ)
    (hhalf : g ≤ ((2*(maxMultiplicity r : ℝ)+(totalMultiplicity r : ℝ))/8)*(t : ℝ)+
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ))
    (hlog : g ≤ ((2*(maxMultiplicity r : ℝ)+3*(totalMultiplicity r : ℝ))/5)*
      (t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))+
        (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ)) :
    g ≤ (r : ℝ)*(t : ℝ)/
      Real.sqrt (Real.logb 2 (r : ℝ)+Real.logb 2 (t : ℝ)) := by
  have hs0 : 0 ≤ Real.logb 2 (r : ℝ) := Real.logb_nonneg (by norm_num)
    (by rcases hr with rfl | rfl | rfl <;> norm_num)
  have hs := log_shift r hr
  rcases hr with rfl | rfl | rfl
  · norm_num [maxMultiplicity,totalMultiplicity] at hhalf hlog
    exact SmallAffineJointLargePrimaryNumerics.five t ht _ g hs0 hs hhalf hlog
  · norm_num [maxMultiplicity,totalMultiplicity] at hhalf hlog
    exact SmallAffineJointLargePrimaryNumerics.seven t ht _ g hs0 hs hhalf hlog
  · norm_num [maxMultiplicity,totalMultiplicity] at hhalf hlog
    exact SmallAffineJointLargePrimaryNumerics.nine t ht _ g hs0 hs hhalf hlog

private theorem tiny_certificate (r : ℕ) (hr : r = 5 ∨ r = 7 ∨ r = 9)
    (t : ℕ) (ht : t ∈ topDegrees) :
    ∃ q : Fin 8, Certificate r (orderBound r) t q := by
  rcases hr with rfl | rfl | rfl
  · exact five_certificates t ht
  · exact SmallAffineJointTinyMoreCertificates.seven_certificates t ht
  · exact SmallAffineJointTinyMoreCertificates.nine_certificates t ht

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

private theorem rank_ceiling_of_real (S : ActualWreathCompressionState Q I)
    (r : ℕ) (hr : 2 ≤ r) (hI : 2 ≤ Fintype.card I)
    (hreal : (MarkedC4.genRank S.A : ℝ) ≤ (r : ℝ)*(Fintype.card I : ℝ)/
      Real.sqrt (Real.logb 2 (r : ℝ)+Real.logb 2 (Fintype.card I : ℝ))) :
    MarkedC4.genRank S.A ≤ traceyPermutationGeneratorCeiling (r*Fintype.card I) := by
  have hlog : Real.logb 2 ((r*Fintype.card I : ℕ) : ℝ) =
      Real.logb 2 (r : ℝ)+Real.logb 2 (Fintype.card I : ℝ) := by
    rw [Nat.cast_mul,Real.logb_mul
      (by exact_mod_cast (show r ≠ 0 by omega))
      (by exact_mod_cast (show Fintype.card I ≠ 0 by omega))]
  have hh : (MarkedC4.genRank S.A : ℝ) ≤ ((r*Fintype.card I : ℕ) : ℝ)/
      Real.sqrt (Real.logb 2 ((r*Fintype.card I : ℕ) : ℝ)) := by
    rw [hlog,Nat.cast_mul]
    exact hreal
  have hf := hh.trans (Nat.le_ceil (((r*Fintype.card I : ℕ) : ℝ)/
    Real.sqrt (Real.logb 2 ((r*Fintype.card I : ℕ) : ℝ))))
  change (MarkedC4.genRank S.A : ℝ) ≤
    (traceyPermutationGeneratorCeiling (r*Fintype.card I) : ℝ) at hf
  exact_mod_cast hf

theorem genRank_le_ceiling (S : ActualWreathCompressionState Q I) (i : I)
    (hI : 2 ≤ Fintype.card I) (r : ℕ) (hr : r = 5 ∨ r = 7 ∨ r = 9)
    (horder : Nat.card S.D ∣ orderBound r)
    (htop : MarkedC4.genRank Q ≤ traceyPermutationGeneratorCeiling (Fintype.card I)) :
    MarkedC4.genRank S.A ≤ traceyPermutationGeneratorCeiling (r*Fintype.card I) := by
  let t := Fintype.card I
  obtain ⟨q,hq,hmax⟩ := LargestPrimePowerEntropy.exists_largest_prime_power t hI
  have hqprime := Nat.prime_of_mem_primeFactors hq
  let a := t.factorization q
  let M := q^a
  have ha : 1 ≤ a := by
    have hh : t.factorization q ≠ 0 := Finsupp.mem_support_iff.mp hq
    dsimp only [a]
    omega
  have hdiv : q^a ∣ Fintype.card I := Nat.ordProj_dvd t q
  have hMt : M ≤ t := Nat.le_of_dvd (by omega : 0 < t) hdiv
  obtain ⟨hN,hC,hm,hmC⟩ := arithmetic_data r hr
  obtain ⟨c,hc,hgen,hcostLog,hcostHalf⟩ := ActualWreathBoundedMultiplicityJointCost.exists_cost
    S i hI (orderBound r) (totalMultiplicity r) (maxMultiplicity r)
    hN horder hC hm hmC q a hqprime ha hdiv hmax
  have htopR : (MarkedC4.genRank Q : ℝ) ≤
      (⌈(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ))⌉₊ : ℝ) := by exact_mod_cast htop
  have hgenR : (MarkedC4.genRank S.A : ℝ) ≤ (c : ℝ)+MarkedC4.genRank Q := by
    exact_mod_cast hgen
  have hr2 : 2 ≤ r := by rcases hr with rfl | rfl | rfl <;> omega
  by_cases hM8 : 8 ≤ M
  · apply rank_ceiling_of_real S r hr2 hI
    exact large_aggregate r hr t (hM8.trans hMt) (MarkedC4.genRank S.A : ℝ)
      (hgenR.trans (add_le_add (hcostHalf hM8) htopR))
      (hgenR.trans (add_le_add hcostLog htopR))
  · have hd := LargestPrimePowerQuadraticEntropy.degree_dvd_lcmUpto t 7 (by omega)
      (by decide) (fun p hp => (hmax p hp).trans (show M ≤ 7 by omega))
    have hd420 : t ∣ 420 := by simpa only [show Nat.lcmUpto 7 = 420 by decide] using hd
    have hmem := mem_topDegrees t hI hd420
    obtain ⟨q',hcert⟩ := tiny_certificate r hr t hmem
    have hcut := ActualWreathBoundedOrderDivisorCost.cost_le_integerCut hc hI
      (orderBound r) hN horder q' (t.factorization q') hcert.1 hcert.2.1
    have htopCut : MarkedC4.genRank Q ≤ topCut t := htop.trans (top_ceiling_le t hmem)
    have hcuts := cuts_le_target r (orderBound r) t q' (by omega) hmem hcert
    exact hgen.trans ((Nat.add_le_add hcut htopCut).trans hcuts)

theorem exists_generating_finset (S : ActualWreathCompressionState Q I) (i : I)
    (hI : 2 ≤ Fintype.card I) (r : ℕ) (hr : r = 5 ∨ r = 7 ∨ r = 9)
    (horder : Nat.card S.D ∣ orderBound r)
    (htop : MarkedC4.genRank Q ≤ traceyPermutationGeneratorCeiling (Fintype.card I)) :
    ∃ F : Finset S.A, Subgroup.closure (F : Set S.A) = ⊤ ∧
      F.card ≤ traceyPermutationGeneratorCeiling (r*Fintype.card I) := by
  obtain ⟨F,hF,hgen⟩ := MarkedC4.genRank_spec (G := S.A)
  exact ⟨F,hgen,hF.le.trans (genRank_le_ceiling S i hI r hr horder htop)⟩

end SymmetricSubgroupAsymptotics.ActualWreathSmallAffineCoarseOrdinaryStep
