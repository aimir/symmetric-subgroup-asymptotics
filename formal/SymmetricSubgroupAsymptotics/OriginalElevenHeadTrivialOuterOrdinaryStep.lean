import SymmetricSubgroupAsymptotics.OriginalNonaffineBlockSocleOrdinaryCost
import SymmetricSubgroupAsymptotics.PrimitiveElevenHeadTrivialOuterOrdinary
import SymmetricSubgroupAsymptotics.ElevenHeadTrivialOuterBlockScaling
import SymmetricSubgroupAsymptotics.NonaffineLocalLargeDegreeOrdinaryAggregate

/-! The original imprimitive source is retained; only its genuinely smaller
transitive top uses induction. No simple coset induction, source order,
index-square estimate, model classification, or global permutation bound is
assumed. The actual raw Y443 consumer supplies all local facts internally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalElevenHeadTrivialOuterOrdinaryStep
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions
open OriginalBlockOrdinaryCompressionState ActualWreathChiefUnitMinimumRate
open ActualWreathPrimitiveSocleOuterOrdinaryCost

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by have h := block.degrees_ge_two.1; omega)
local instance stateComponentAction : MulAction (initialState J block).D block.Fibre :=
  inferInstanceAs (MulAction block.Component block.Fibre)
local instance stateComponentFaithful : FaithfulSMul (initialState J block).D block.Fibre :=
  inferInstanceAs (FaithfulSMul block.Component block.Fibre)
local instance stateComponentPrimitive : MulAction.IsPreprimitive (initialState J block).D block.Fibre :=
  block.component_preprimitive

variable (D : NonaffineData block.Component block.Fibre)

private theorem degree_ge_sixty (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (hl : 27 ≤ ell) (hk : 2 ≤ D.factorCount) : 60 ≤ Nat.card block.Fibre := by
  have ho := NonabelianSimpleOrderAtLeastSixty.sixty_le_card D.Simple D.noncommutative
  rcases D.degreeForm hell with ⟨a,ha,he⟩ | ⟨a,ha,he⟩
  · have ha27 : 27 ≤ a := hl.trans ha
    have hp : 27^2 ≤ a^D.factorCount :=
      (Nat.pow_le_pow_left ha27 2).trans
        (Nat.pow_le_pow_right (by omega : 0 < a) hk)
    rw [←he] at hp
    have hp' : 729 ≤ Nat.card block.Fibre := by
      simpa only [show (27 : ℕ)^2=729 by decide] using hp
    exact (by decide : 60 ≤ 729).trans hp'
  · have ha1 : 1 ≤ a := by omega
    have hp : Nat.card D.Simple ≤ (Nat.card D.Simple)^a := by
      simpa only [pow_one] using Nat.pow_le_pow_right (Nat.card_pos (α := D.Simple)) ha1
    exact ho.trans (hp.trans_eq he.symm)

private theorem seven_power_le_degree (ell : ℕ) (hell : LeastProperIndex D.Simple ell)
    (hl : 27 ≤ ell) : 7^D.factorCount ≤ Nat.card block.Fibre := by
  have ho := NonabelianSimpleOrderAtLeastSixty.sixty_le_card D.Simple D.noncommutative
  have hform : PrimitiveSocleDegreeForm 7 (Nat.card D.Simple) D.factorCount
      (Nat.card block.Fibre) := by
    rcases D.degreeForm hell with ⟨a,ha,he⟩ | ⟨a,ha,he⟩
    · exact Or.inl ⟨a,by omega,he⟩
    · exact Or.inr ⟨a,ha,he⟩
  exact primitiveSocle_power_le_degree (by decide) (by omega) hform

/-- Structural local facts concern the selected SAME factor. No fitted
inequality is supplied; the uniform scalar bounds are proved below. -/
theorem genRank_le_ceiling (i : block.Points)
    (hhead : MarkedC4.genRank D.Simple ≤ 11)
    (houter : Nat.card (Outer D.Simple)=1)
    (ell : ℕ) (hell : LeastProperIndex D.Simple ell) (hl : 27 ≤ ell)
    (hbelow : SmallerTransitiveRankBound n) :
    MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling n := by
  let r := Nat.card block.Fibre
  let t := Nat.card block.Points
  let H : ℕ := if D.factorCount=1 then 11 else 22
  let B := outerMultiplicity (initialState J block) D
  have ht : 2 ≤ t := block.degrees_ge_two.2
  have hr : 2 ≤ r := block.degrees_ge_two.1
  have hr27 : 27 ≤ r := hl.trans
    (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell)
  have hB : B=ArithmeticFunction.cardFactors D.factorCount.factorial := by
    simp only [B,outerMultiplicity,houter,ArithmeticFunction.cardFactors_one,mul_zero,zero_add]
  have htop : (MarkedC4.genRank block.Top : ℝ) ≤ traceyPermutationGeneratorCeiling t := by
    letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
    exact_mod_cast rank_of_faithful_transitive_action n hbelow block.Top block.Points
      block.degrees_ge_two.2 (by simpa only [Nat.card_fin] using block.degrees_lt.2)
  have hsource : (MarkedC4.genRank J : ℝ) ≤ (H : ℝ)+(B : ℝ)*rate t+
      traceyPermutationGeneratorCeiling t := by
    have hheadR : (MarkedC4.genRank D.Simple : ℝ) ≤ 11 := by exact_mod_cast hhead
    by_cases hk : D.factorCount=1
    · have hI : 2 ≤ Fintype.card block.Points := by
        simpa only [Fintype.card_eq_nat_card] using ht
      have hs := genRank_le_simple_add_outer_rate_of_one_factor
        (initialState J block) D i hI hk
      simp only [Fintype.card_eq_nat_card] at hs
      change (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank D.Simple : ℝ)+
        (B : ℝ)*rate t+MarkedC4.genRank block.Top at hs
      have hH : H=11 := if_pos hk
      rw [hH]
      norm_num only [Nat.cast_ofNat]
      linarith only [hs,hheadR,htop]
    · have hs := OriginalNonaffineBlockSocleOrdinaryCost.source_genRank_le_socle_cost J block D i
      change (MarkedC4.genRank J : ℝ) ≤ 2*(MarkedC4.genRank D.Simple : ℝ)+
        (B : ℝ)*rate t+MarkedC4.genRank block.Top at hs
      have hH : H=22 := if_neg hk
      rw [hH]
      norm_num only [Nat.cast_ofNat]
      linarith only [hs,hheadR,htop]
  have hH22 : H ≤ 22 := by dsimp only [H]; split_ifs <;> omega
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hreal : (MarkedC4.genRank J : ℝ) ≤
      (r : ℝ)*(t : ℝ)/Real.sqrt (Real.logb 2 ((r : ℝ)*(t : ℝ))) := by
    by_cases hlarge : 1024 ≤ r
    · have hp := FiniteModelPrimitiveOrdinaryBudget.two_pow_factorCount_le_degree D
      have hklog : (D.factorCount : ℝ) ≤ Real.logb 2 (r : ℝ) := by
        have hh := IntegerLogSquareRootCeilingCertificate.log_lower r 1 D.factorCount
          (by omega) (by decide) (by simpa only [pow_one] using hp)
        simpa only [Nat.cast_one,div_one] using hh
      have hbNat : B ≤ D.factorCount^2 := by
        rw [hB]
        exact FiniteModelPrimitiveOrdinaryBudget.factorial_cardFactors_le_square _
      have hbR : (B : ℝ) ≤ (D.factorCount : ℝ)^2 := by exact_mod_cast hbNat
      have hL : 0 ≤ Real.logb 2 (r : ℝ) := (Nat.cast_nonneg D.factorCount).trans hklog
      have hb : (B : ℝ) ≤ (Real.logb 2 (r : ℝ))^2+5*Real.logb 2 (r : ℝ) := by
        have hh := (sq_le_sq₀ (Nat.cast_nonneg D.factorCount) hL).mpr hklog
        nlinarith only [hbR,hh,hL]
      have hroot : (11 : ℝ) ≤ Real.sqrt (r : ℝ) := by
        apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
        have hrR : (1024 : ℝ) ≤ r := by exact_mod_cast hlarge
        nlinarith only [hrR]
      have hH : (H : ℝ) ≤ 2*Real.sqrt (r : ℝ) := by
        have hh : (H : ℝ) ≤ 22 := by exact_mod_cast hH22
        linarith only [hh,hroot]
      have hc := NonaffineLocalLargeDegreeOrdinaryAggregate.square_root_cost_le r t hlarge ht
        (B : ℝ) hB0 hb
      have hh : (MarkedC4.genRank J : ℝ) ≤ 2*Real.sqrt (r : ℝ)+
          (B : ℝ)*rate t+traceyPermutationGeneratorCeiling t := by
        linarith only [hsource,hH]
      exact hh.trans hc
    · have hsmall : r < 1024 := by omega
      have hband : (27 ≤ r ∧ (H : ℝ) ≤ 11 ∧ (B : ℝ)=0) ∨
          (60 ≤ r ∧ (H : ℝ) ≤ 22 ∧ (B : ℝ) ≤ 2) := by
        by_cases hk : D.factorCount=1
        · have hH : H=11 := if_pos hk
          have hBzero : B=0 := by rw [hB,hk]; decide +kernel
          exact Or.inl ⟨hr27,by rw [hH]; norm_num,by rw [hBzero]; norm_num⟩
        · have hk2 : 2 ≤ D.factorCount := by have hh := D.factorCount_pos; omega
          have hp := seven_power_le_degree J block D ell hell hl
          have hk4 : D.factorCount < 4 := by
            by_contra hh
            have hh4 : 7^4 ≤ 7^D.factorCount := Nat.pow_le_pow_right (by decide) (by omega)
            have hbad := hh4.trans hp
            change 2401 ≤ r at hbad
            omega
          have hBtwo : B ≤ 2 := by
            rw [hB]
            have hk23 : D.factorCount=2 ∨ D.factorCount=3 := by omega
            rcases hk23 with hh | hh <;> rw [hh] <;> decide +kernel
          exact Or.inr ⟨degree_ge_sixty J block D ell hell hl hk2,
            by exact_mod_cast hH22,by exact_mod_cast hBtwo⟩
      exact hsource.trans (ElevenHeadTrivialOuterBlockScaling.small_local_cost_le
        r t hr hsmall ht (H : ℝ) (B : ℝ) (by positivity) hB0 hband)
  have hproduct : r*t=n := by simpa only [Nat.card_fin] using block.degree_product
  have hproductR : (r : ℝ)*(t : ℝ)=(n : ℝ) := by exact_mod_cast hproduct
  rw [hproductR] at hreal
  have hh := hreal.trans (Nat.le_ceil ((n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))))
  change (MarkedC4.genRank J : ℝ) ≤ (traceyPermutationGeneratorCeiling n : ℝ) at hh
  exact_mod_cast hh

end SymmetricSubgroupAsymptotics.OriginalElevenHeadTrivialOuterOrdinaryStep
