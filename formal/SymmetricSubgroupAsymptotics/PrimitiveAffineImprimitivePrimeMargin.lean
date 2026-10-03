import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveGenericMargin
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.UniqueMinimalNormalAbelianLength
import SymmetricSubgroupAsymptotics.ActualWreathCompressionWeightedBudget
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Prime local degrees below twenty-five

For a primitive affine component of prime degree `r`, the regular translation
group has order `r` and the point stabilizer embeds in its automorphism group,
of order `r - 1`.  Hence the literal component order divides `r(r-1)`.
The number of abelian chief edges in the actual wreath trace is consequently
at most `Ω(r(r-1))`.  At the five primes from eleven through twenty-three this
coarse but intrinsic bound already leaves the required pre-`E7` margin.

Degree seven uses the exact prime-weighted order budget of the literal
component.  The five larger primes already close under the coarser number of
abelian composition factors.
-/

set_option autoImplicit false
noncomputable section
open scoped ArithmeticFunction.Omega Classical

namespace SymmetricSubgroupAsymptotics

/-- The total number of prime factors is monotone under nonzero divisibility. -/
theorem cardFactors_le_of_dvd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a ∣ b) :
    ArithmeticFunction.cardFactors a ≤ ArithmeticFunction.cardFactors b := by
  obtain ⟨k, rfl⟩ := h
  have hk : k ≠ 0 := by
    intro hk
    apply hb
    simp [hk]
  rw [ArithmeticFunction.cardFactors_mul ha hk]
  omega

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)

/-- At prime local degree the literal affine component order divides
`r(r-1)`.  This uses the actual regular subgroup and actual point stabilizer;
no abstract affine overgroup is substituted. -/
theorem component_card_dvd_prime_mul_pred
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hr : (Nat.card block.Fibre).Prime) :
    Nat.card block.Component ∣
      Nat.card block.Fibre * (Nat.card block.Fibre - 1) := by
  let r := Nat.card block.Fibre
  let x : block.Fibre := ⟨basePoint, block.map_base⟩
  have hp : P.p = r := by
    letI : Fact P.p.Prime := ⟨P.p_prime⟩
    obtain ⟨d, hd⟩ := IsPGroup.exists_card_eq P.V_pgroup
    have hpow : r = P.p ^ d := by
      calc
        r = Nat.card block.Fibre := rfl
        _ = Nat.card P.V := (P.card_eq x).symm
        _ = P.p ^ d := hd
    exact (hr.pow_eq_iff.mp hpow.symm).1
  have hVcard : Nat.card P.V = r := by
    calc
      Nat.card P.V = Nat.card block.Fibre := P.card_eq x
      _ = r := rfl
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hcyclic : IsCyclic P.V := by
    exact isCyclic_of_prime_card (hVcard.trans hp.symm)
  letI : IsCyclic P.V := hcyclic
  have hcomp : Nat.card (P.complement x) ∣ Nat.card (MulAut P.V) :=
    Subgroup.card_dvd_of_injective (P.complementAction x)
      (P.complementAction_injective x)
  have hAut : Nat.card (MulAut P.V) = r - 1 := by
    rw [IsCyclic.card_mulAut, hVcard, Nat.totient_prime hr]
  have hcomp' : Nat.card (P.complement x) ∣ r - 1 := by
    simpa only [hAut] using hcomp
  have hfactor := (P.isComplement'_complement x).card_mul
  rw [hVcard] at hfactor
  rw [← hfactor]
  exact Nat.mul_dvd_mul_left r hcomp'

/-- The actual traced tower has at most `Ω(r(r-1))` abelian composition
edges at a prime local degree. -/
theorem trace_abelianLength_le_prime_mul_pred
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : (Nat.card block.Fibre).Prime) :
    let T := ComponentSource.trace hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm block P
    T.tower.abelianLength ≤ ArithmeticFunction.cardFactors
      (Nat.card block.Fibre * (Nat.card block.Fibre - 1)) := by
  let T := ComponentSource.trace hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P
  have hchief : actualChiefSeriesAbelianLength T.chief ≤
      ArithmeticFunction.cardFactors (Nat.card block.Component) :=
    actualChiefSeriesAbelianLength_le_cardFactors T.chief
  have hdvd := component_card_dvd_prime_mul_pred block P hr
  have hmono := cardFactors_le_of_dvd
    (Nat.card_pos (α := block.Component)).ne'
    (Nat.mul_ne_zero hr.ne_zero (Nat.sub_ne_zero_of_lt hr.one_lt)) hdvd
  dsimp only
  rw [T.abelianLength_eq]
  exact hchief.trans hmono

/-- The five prime degrees strictly between seven and twenty-five satisfy
the required affine capacity margin using only the component-order divisor. -/
theorem primeElevenToTwentyThree_margin
    (r s w K : ℕ) (hs : 2 ≤ s) (hw : w = r * s)
    (hr : r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 ∨ r = 23)
    (hK : K ≤ ArithmeticFunction.cardFactors (r * (r - 1)))
    (eta : ℝ)
    (heta : eta ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) * K) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - s) / 8 - eta := by
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have homega : ArithmeticFunction.cardFactors 110 = 3 := by native_decide
    rw [homega] at hK
    have hKR : (K : ℝ) ≤ 3 := by exact_mod_cast hK
    have heta' : eta < (17 / 32 : ℝ) * (s / 2) * 3 := by
      calc
        eta ≤ fixedTargetCompositionGamma * (s / 2) * K := heta
        _ ≤ fixedTargetCompositionGamma * (s / 2) * 3 := by
          exact mul_le_mul_of_nonneg_left hKR
            (mul_nonneg hgamma0 (by positivity))
        _ < (17 / 32 : ℝ) * (s / 2) * 3 := by
          exact mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_right hgamma (by positivity)) (by norm_num)
    have hwR : (w : ℝ) = 11 * s := by exact_mod_cast hw
    unfold preE7CharacterRho
    rw [hwR]
    nlinarith

  · have homega : ArithmeticFunction.cardFactors 156 = 4 := by native_decide
    rw [homega] at hK
    have hKR : (K : ℝ) ≤ 4 := by exact_mod_cast hK
    have heta' : eta < (17 / 32 : ℝ) * (s / 2) * 4 := by
      calc
        eta ≤ fixedTargetCompositionGamma * (s / 2) * K := heta
        _ ≤ fixedTargetCompositionGamma * (s / 2) * 4 := by
          exact mul_le_mul_of_nonneg_left hKR
            (mul_nonneg hgamma0 (by positivity))
        _ < (17 / 32 : ℝ) * (s / 2) * 4 := by
          exact mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_right hgamma (by positivity)) (by norm_num)
    have hwR : (w : ℝ) = 13 * s := by exact_mod_cast hw
    unfold preE7CharacterRho
    rw [hwR]
    nlinarith
  · have homega : ArithmeticFunction.cardFactors 272 = 5 := by native_decide
    rw [homega] at hK
    have hKR : (K : ℝ) ≤ 5 := by exact_mod_cast hK
    have heta' : eta < (17 / 32 : ℝ) * (s / 2) * 5 := by
      calc
        eta ≤ fixedTargetCompositionGamma * (s / 2) * K := heta
        _ ≤ fixedTargetCompositionGamma * (s / 2) * 5 := by
          exact mul_le_mul_of_nonneg_left hKR
            (mul_nonneg hgamma0 (by positivity))
        _ < (17 / 32 : ℝ) * (s / 2) * 5 := by
          exact mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_right hgamma (by positivity)) (by norm_num)
    have hwR : (w : ℝ) = 17 * s := by exact_mod_cast hw
    unfold preE7CharacterRho
    rw [hwR]
    nlinarith
  · have homega : ArithmeticFunction.cardFactors 342 = 4 := by native_decide
    rw [homega] at hK
    have hKR : (K : ℝ) ≤ 4 := by exact_mod_cast hK
    have heta' : eta < (17 / 32 : ℝ) * (s / 2) * 4 := by
      calc
        eta ≤ fixedTargetCompositionGamma * (s / 2) * K := heta
        _ ≤ fixedTargetCompositionGamma * (s / 2) * 4 := by
          exact mul_le_mul_of_nonneg_left hKR
            (mul_nonneg hgamma0 (by positivity))
        _ < (17 / 32 : ℝ) * (s / 2) * 4 := by
          exact mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_right hgamma (by positivity)) (by norm_num)
    have hwR : (w : ℝ) = 19 * s := by exact_mod_cast hw
    unfold preE7CharacterRho
    rw [hwR]
    nlinarith
  · have homega : ArithmeticFunction.cardFactors 506 = 3 := by native_decide
    rw [homega] at hK
    have hKR : (K : ℝ) ≤ 3 := by exact_mod_cast hK
    have heta' : eta < (17 / 32 : ℝ) * (s / 2) * 3 := by
      calc
        eta ≤ fixedTargetCompositionGamma * (s / 2) * K := heta
        _ ≤ fixedTargetCompositionGamma * (s / 2) * 3 := by
          exact mul_le_mul_of_nonneg_left hKR
            (mul_nonneg hgamma0 (by positivity))
        _ < (17 / 32 : ℝ) * (s / 2) * 3 := by
          exact mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_right hgamma (by positivity)) (by norm_num)
    have hwR : (w : ℝ) = 23 * s := by exact_mod_cast hw
    unfold preE7CharacterRho
    rw [hwR]
    nlinarith

theorem weightedAbelianFactorBudget_fortyTwo :
    weightedAbelianFactorBudget 42 =
      (1 : ℝ) / 2 + Real.logb 2 3 / 3 + Real.logb 2 7 / 7 := by
  have h2 : weightedAbelianFactorBudget 2 =
      (1 : ℝ) * (Real.logb 2 2 / 2) := by
    simpa using weightedAbelianFactorBudget_prime_pow
      (p := 2) (a := 1) Nat.prime_two
  have h3 : weightedAbelianFactorBudget 3 =
      (1 : ℝ) * (Real.logb 2 3 / 3) := by
    simpa using weightedAbelianFactorBudget_prime_pow
      (p := 3) (a := 1) Nat.prime_three
  have h7 : weightedAbelianFactorBudget 7 =
      (1 : ℝ) * (Real.logb 2 7 / 7) := by
    simpa using weightedAbelianFactorBudget_prime_pow
      (p := 7) (a := 1) (by norm_num)
  rw [show 42 = 2 * 21 by norm_num,
    weightedAbelianFactorBudget_mul (by norm_num) (by norm_num),
    show 21 = 3 * 7 by norm_num,
    weightedAbelianFactorBudget_mul (by norm_num) (by norm_num),
    h2, h3, h7, Real.logb_self_eq_one (by norm_num)]
  ring

private theorem logb_two_seven_lt_three : Real.logb 2 7 < 3 := by
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 7) (by norm_num : (7 : ℝ) < 8)
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at h
  norm_num at h ⊢
  exact h

/-- Degree seven closes at the exact retained prime weights of the divisor
`42`; the odd block-count parity loss is kept explicitly. -/
theorem primeSeven_weightedMargin
    (s w : ℕ) (hs : 2 ≤ s) (hw : w = 7 * s)
    (eta : ℝ)
    (heta : eta ≤ ((s / 2 : ℕ) : ℝ) * weightedAbelianFactorBudget 42) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - s) / 8 - eta := by
  have hthree := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo
  have hseven := logb_two_seven_lt_three
  have hbudget : weightedAbelianFactorBudget 42 < (327 : ℝ) / 224 := by
    rw [weightedAbelianFactorBudget_fortyTwo]
    unfold fixedTargetCompositionGamma at hthree
    nlinarith
  have heta' : eta < ((s / 2 : ℕ) : ℝ) * ((327 : ℝ) / 224) :=
    heta.trans_lt (mul_lt_mul_of_pos_left hbudget (by
      exact_mod_cast (Nat.div_pos hs (by norm_num : 0 < 2))))
  have hwR : (w : ℝ) = 7 * s := by exact_mod_cast hw
  by_cases hsevenEven : Even s
  · have hweven : Even w := by
      rw [hw]
      exact Even.mul_left hsevenEven 7
    have hew : evenWidth w = w := by
      rcases hweven with ⟨k, rfl⟩
      unfold evenWidth halfDegree
      omega
    obtain ⟨k, hk⟩ := hsevenEven
    have hdiv : s / 2 = k := by omega
    have hhalf : (((s / 2 : ℕ) : ℝ)) = (s : ℝ) / 2 := by
      rw [hdiv, hk]
      push_cast
      ring
    unfold preE7CharacterRho
    rw [hhalf] at heta'
    rw [hew, hwR]
    nlinarith
  · have hsOdd : Odd s := Nat.not_even_iff_odd.mp hsevenEven
    obtain ⟨k, hk⟩ := hsOdd
    have hs3 : 3 ≤ s := by
      have hspos : 0 < s := by omega
      omega
    have hweven : evenWidth w = w - 1 := by
      rw [hw]
      rw [hk]
      unfold evenWidth halfDegree
      omega
    have hdiv : s / 2 = k := by omega
    have hhalf : (((s / 2 : ℕ) : ℝ)) = ((s : ℝ) - 1) / 2 := by
      rw [hdiv, hk]
      push_cast
      ring
    unfold preE7CharacterRho
    rw [hhalf] at heta'
    rw [hweven, hwR]
    have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs3
    have hwpos : 1 ≤ w := by omega
    rw [Nat.cast_sub hwpos]
    norm_num
    nlinarith

namespace ComponentSource

variable
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)

/-- Construction-facing source for prime local degrees `11,13,17,19,23`. -/
noncomputable def of_primeElevenToTwentyThree
    (hrPrime : (Nat.card block.Fibre).Prime)
    (hr11 : 11 ≤ Nat.card block.Fibre)
    (hr25 : Nat.card block.Fibre < 25) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P where
  margin := by
    letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    let r := Nat.card block.Fibre
    let s := Nat.card block.Points
    let T := trace hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    have hrCases : r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 ∨ r = 23 := by
      change 11 ≤ r at hr11
      change r < 25 at hr25
      change r.Prime at hrPrime
      interval_cases r <;> norm_num at hrPrime <;> simp_all
    have hlen := trace_abelianLength_le_prime_mul_pred block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hrPrime
    have heta : T.tower.envelope.eta ≤
        fixedTargetCompositionGamma * ((s : ℝ) / 2) *
          T.tower.abelianLength := by
      simpa only [s, Fintype.card_eq_nat_card] using
        ActualWreathCompressionTower.envelope_eta_le_abelianLength T.tower
    have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
      unfold fixedTargetCompositionGamma
      exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num))
        (by norm_num)
    have heta' : T.tower.envelope.eta ≤
        fixedTargetCompositionGamma * ((s : ℝ) / 2) *
          ArithmeticFunction.cardFactors (r * (r - 1)) := by
      exact heta.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen)
        (mul_nonneg hgamma0 (by positivity)))
    have hv : T.tower.envelope.v = s := by
      simpa only [s, Fintype.card_eq_nat_card] using
        ActualWreathCompressionTower.envelope_v T.tower
    change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - T.tower.envelope.v) / 8 - T.tower.envelope.eta
    rw [hv]
    apply primeElevenToTwentyThree_margin r s w
      (ArithmeticFunction.cardFactors (r * (r - 1)))
      block.degrees_ge_two.2 (width_eq block) hrCases le_rfl
    exact heta'

/-- Construction-facing source at local degree seven, using the exact
prime-weighted divisor `|L| ∣ 42`. -/
noncomputable def of_primeSeven
    (hr : Nat.card block.Fibre = 7) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P where
  margin := by
    letI : Nontrivial block.Fibre :=
      Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    let s := Nat.card block.Points
    let T := trace hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    have hrPrime : (Nat.card block.Fibre).Prime := by
      rw [hr]
      norm_num
    have hdiv : Nat.card block.Component ∣ 42 := by
      have h := component_card_dvd_prime_mul_pred block P hrPrime
      simpa only [hr] using h
    have hbudget : weightedAbelianFactorBudget (Nat.card block.Component) ≤
        weightedAbelianFactorBudget 42 :=
      weightedAbelianFactorBudget_mono_of_dvd
        (Nat.card_pos (α := block.Component)).ne' (by norm_num) hdiv
    have htdiv : T.tower.localFactorOrderProduct ∣ 42 := by
      rw [T.tower.localFactorOrderProduct_eq_card]
      exact hdiv
    have heta0 :=
      ActualWreathCompressionTower.envelope_eta_le_natHalf_weightedAbelianBudget_of_squarefree
        T.tower T.integralCapacities 42 (by norm_num) (by native_decide) htdiv
    have heta : T.tower.envelope.eta ≤
        ((s / 2 : ℕ) : ℝ) * weightedAbelianFactorBudget 42 := by
      refine heta0.trans ?_
      have hweighted := T.tower.weightedAbelianBudget_le_factorBudget
      calc
        ((Fintype.card block.Points / 2 : ℕ) : ℝ) *
              T.tower.weightedAbelianBudget ≤
            ((Fintype.card block.Points / 2 : ℕ) : ℝ) *
              weightedAbelianFactorBudget T.tower.localFactorOrderProduct :=
          mul_le_mul_of_nonneg_left hweighted (by positivity)
        _ ≤ ((Fintype.card block.Points / 2 : ℕ) : ℝ) *
              weightedAbelianFactorBudget 42 :=
          mul_le_mul_of_nonneg_left (by
            rw [T.tower.localFactorOrderProduct_eq_card]
            exact hbudget) (by positivity)
        _ = ((s / 2 : ℕ) : ℝ) * weightedAbelianFactorBudget 42 := by
          simp only [s, Fintype.card_eq_nat_card]
    have hv : T.tower.envelope.v = s := by
      simpa only [s, Fintype.card_eq_nat_card] using
        ActualWreathCompressionTower.envelope_v T.tower
    change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - T.tower.envelope.v) / 8 - T.tower.envelope.eta
    rw [hv]
    apply primeSeven_weightedMargin s w block.degrees_ge_two.2
    · simpa only [hr] using width_eq block
    · exact heta

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
