import SymmetricSubgroupAsymptotics.SemisimpleArbitraryFusionEnvelope
import SymmetricSubgroupAsymptotics.LocalSemisimpleRoundingCompression

/-! Predicate-independent semisimple fusion rows for arbitrary literal
permutation actions. The comparator, full original normal-axis sum, actual
untouched complement, exact hot/cold kernels and fixedrho margin are retained.
No non-pair/no-C3 action-class membership is required. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open Non2UnipotentPrefixFiniteMenu

structure SemisimpleRoundingFusionData (w : ℕ)
    (U : Subgroup (Equiv.Perm (Fin w))) extends
    LocalSemisimpleRoundingCompressionData U w where
  width_lower : 5≤w

namespace SemisimpleRoundingFusionData
variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    (D : SemisimpleRoundingFusionData w U)

theorem quotientDegree_margin :
    preE7CharacterRho*w≤((evenWidth w : ℝ)-(max 2 D.quotientDegree : ℕ))/8 :=
  PreE7SemisimpleMarginData.margin_of_rounding_gap D.degree_bound D.quotientDegree_gap

/-- Seed degree two also covers the trivial compressed quotient. -/
def seedDegree : ℕ := max 2 D.quotientDegree

def degree : ℕ :=
  paddedComparatorDegree preE7CharacterRho D.seedDegree w

def delta : ℝ :=
  paddedComparatorDelta preE7CharacterRho 0 D.seedDegree w

def cutoff : ℝ := (D.degree : ℝ) / 8 + D.delta / 2

def paddedAction :
    (U ⧸ D.E) →* Equiv.Perm (Fin D.degree) :=
  (characterComparatorPadHom
    ((le_max_right 2 D.quotientDegree).trans (le_max_left _ _))).comp
      D.quotientAction

theorem paddedAction_injective : Function.Injective D.paddedAction :=
  (characterComparatorPadHom_injective _).comp
    D.quotientAction_injective

def coefficient (b : ℕ) : ℝ :=
  D.chart.outerFactor (Real.logb 2 (Nat.factorial b))

theorem seedDegree_two_le : 2 ≤ D.seedDegree := by
  simp [seedDegree]

theorem padded_margin :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - D.seedDegree) / 8 := D.quotientDegree_margin

theorem coefficient_nonneg (b : ℕ) : 0 ≤ D.coefficient b :=
  D.chart.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.factorial_pos b))

private theorem logb_two_sq_le_four_log_sq (x : ℝ) :
    (Real.logb 2 x) ^ 2 ≤ 4 * (Real.log x) ^ 2 := by
  have hlog : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogsq : (1 / 4 : ℝ) ≤ (Real.log 2) ^ 2 := by
    nlinarith
  have hlog0 : 0 < Real.log 2 := lt_trans (by norm_num) hlog
  have hden : 0 < (Real.log 2) ^ 2 := sq_pos_of_pos hlog0
  unfold Real.logb
  rw [div_pow]
  apply (div_le_iff₀ hden).2
  have hsquare : 0 ≤ (Real.log x) ^ 2 := sq_nonneg _
  nlinarith

theorem coefficient_bound
    (hOuter : SemisimpleOuterFactorPermutationBound) (b : ℕ) :
    D.coefficient b ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  have hsource := hOuter w U D.E D.chart b
  apply hsource.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hw : (0 : ℝ) ≤ w := by positivity
  have hsquare := logb_two_sq_le_four_log_sq
    (((w + b + 2 : ℕ) : ℝ))
  nlinarith

theorem outer_bound (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    D.chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
      D.coefficient b * (2 : ℝ) ^ ((0 : ℝ) * b) := by
  have hlog :
      Real.logb 2 (Nat.card J) ≤ Real.logb 2 (Nat.factorial b) := by
    apply Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast Nat.card_pos)
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : J → Equiv.Perm (Fin b)) Subtype.val_injective
    rw [Nat.card_perm, Nat.card_fin] at hcard
    exact_mod_cast hcard
  have hfactor :
      D.chart.outerFactor (Real.logb 2 (Nat.card J)) ≤
        D.chart.outerFactor (Real.logb 2 (Nat.factorial b)) := by
    unfold SemisimpleNormalChart.outerFactor
    apply Finset.prod_le_prod
    · intro k _
      exact add_nonneg zero_le_one
        (D.chart.factorWeight_nonneg
          (Real.logb_nonneg (by norm_num)
            (by exact_mod_cast Nat.card_pos)) k)
    · intro k _
      simpa only [add_comm] using add_le_add_left
        (D.chart.factorWeight_mono hlog k) 1
  simpa only [zero_mul, Real.rpow_zero, mul_one, coefficient] using hfactor

theorem entryParameters :
    PreE7CharacterEntryParameters preE7CharacterRho w D.degree 0 D.delta
      D.cutoff D.cutoff 0 := by
  simpa [degree, delta, cutoff] using
    (preE7Padded_entryParameters (w := w) (v0 := D.seedDegree) (eta := 0)
      (by norm_num) D.seedDegree_two_le (by simpa using D.padded_margin))

/-- All original normal axes are paid together, for every predicate. -/
theorem source_bound (b : ℕ)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum U P J≤
      (D.coefficient b*(2 : ℝ)^((0 : ℝ)*b))*
        completeQuotientWeight (R := U⧸D.E) J := by
  have hs := D.chart.fusionCompleteSourceSum_le U D.E P J
  have hf := D.outer_bound b J
  have hw : 0≤completeQuotientWeight (R := U⧸D.E) J := completeQuotientWeight_nonneg J
  exact hs.trans (by
    calc
      _ ≤ completeQuotientWeight (R := U⧸D.E) J *
          (D.coefficient b*(2 : ℝ)^((0 : ℝ)*b)) :=
        mul_le_mul_of_nonneg_left hf hw
      _ = _ := by ring)

/-- The complete physical fusion bound retains the literal deleted action,
the whole untouched complement and its exact normalizer divisor. -/
theorem kernel_bound (b : ℕ)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ)/
      exactBenchmark (b+w)≤
    growingQuotientHotKernel (fun n => (subgroupCount n : ℝ))
      b w D.degree (D.coefficient b)
      (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w)))) : ℝ)
      0 D.delta D.cutoff +
    fusionWidthColdKernel b w (D.coefficient b)
      (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin w)))) : ℝ)
      D.cutoff*((subgroupCount b : ℝ)/exactBenchmark b) := by
  have h := fusionPhysical_growingQuotient_additiveTail_kernel_bound
    U P hP D.paddedAction D.paddedAction_injective
    (D.coefficient b) 0 0 0 D.delta D.cutoff (D.coefficient_nonneg b) le_rfl (by
      intro J
      simpa only [zero_mul,add_zero] using D.source_bound b P J)
  simpa only [zero_add,fusionWidthColdKernel,zero_div,mul_zero,zero_mul,add_zero] using h

end SemisimpleRoundingFusionData
end SymmetricSubgroupAsymptotics
