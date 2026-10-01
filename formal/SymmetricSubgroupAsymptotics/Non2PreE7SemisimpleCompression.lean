import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2MenuMass
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Complete semisimple compression at the T1 boundary

Let `E ◁ U` be a literal semisimple normal subgroup.  If `U/E` has a
faithful permutation action whose degree is at most half the even width,
the uniform semisimple outer-factor theorem supplies a complete-source
`.comp` certificate.  The normal-axis sum stays correlated throughout.

This is the numerical half of the manuscript's complete semisimple
compression theorem.  The remaining structural half must construct `E`,
its chart and the small quotient action from an exact primitive component.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Literal structural data needed by complete semisimple compression. -/
structure PreE7SemisimpleCompressionData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  quotientDegree : ℕ
  quotientAction :
    (preE7NonPairAction w i ⧸ E) →* Equiv.Perm (Fin quotientDegree)
  quotientAction_injective : Function.Injective quotientAction
  quotientDegree_small : 2 * quotientDegree ≤ evenWidth w

attribute [instance] PreE7SemisimpleCompressionData.E_normal

namespace PreE7SemisimpleCompressionData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7SemisimpleCompressionData w i)

/-- Seed degree two also covers the trivial compressed quotient. -/
def seedDegree : ℕ := max 2 D.quotientDegree

def degree : ℕ :=
  paddedComparatorDegree preE7CharacterRho D.seedDegree w

def delta : ℝ :=
  paddedComparatorDelta preE7CharacterRho 0 D.seedDegree w

def cutoff : ℝ := (D.degree : ℝ) / 8 + D.delta / 2

def paddedAction :
    (preE7NonPairAction w i ⧸ D.E) →* Equiv.Perm (Fin D.degree) :=
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

theorem seedDegree_small : 2 * D.seedDegree ≤ evenWidth w := by
  have heven : 4 ≤ evenWidth w := by
    have hwidth : w ≤ evenWidth w + 1 := width_le_evenWidth_add_one w
    have hw : 5 ≤ w := D.width_lower
    omega
  unfold seedDegree
  by_cases hq : D.quotientDegree ≤ 2
  · rw [max_eq_left hq]
    exact heven
  · rw [max_eq_right (by omega)]
    exact D.quotientDegree_small

theorem padded_margin :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - D.seedDegree) / 8 := by
  have hseed : (2 : ℝ) * D.seedDegree ≤ evenWidth w := by
    exact_mod_cast D.seedDegree_small
  have heven : (4 : ℝ) ≤ evenWidth w := by
    exact_mod_cast (show 4 ≤ evenWidth w by
      have hwidth : w ≤ evenWidth w + 1 := width_le_evenWidth_add_one w
      have hw : 5 ≤ w := D.width_lower
      omega)
  have hwidth : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  unfold preE7CharacterRho
  norm_num
  nlinarith

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
  have hsource := hOuter w (preE7NonPairAction w i) D.E D.chart b
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

/-- The complete correlated numerical certificate, under the published
uniform outer-factor input. -/
noncomputable def completeSourceData
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    PreE7SemisimpleCompleteSourceData .comp w i where
  E := D.E
  E_normal := D.E_normal
  chart := D.chart
  v := D.degree
  action := D.paddedAction
  action_injective := D.paddedAction_injective
  coefficient := D.coefficient
  eta := 0
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.cutoff
  theta := 0
  alpha_eq := by simp
  coefficient_nonneg := D.coefficient_nonneg
  parameters := D.entryParameters
  coefficient_bound := D.coefficient_bound hOuter
  outer_bound := D.outer_bound

/-- Complete semisimple compression is a concrete `.comp` owner at the
source-level T1 exhaustion boundary. -/
noncomputable def toRankTailOwnerSource
    (hOuter : SemisimpleOuterFactorPermutationBound) :
    PreE7RankTailOwnerSourceData w i :=
  (D.completeSourceData hOuter).toRankTailOwnerSource

end PreE7SemisimpleCompressionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
