import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleCompression

/-! Semisimple compression needs the actual padding margin, not the stronger
half-degree estimate used by the old certificate. This independent adapter
retains the actual normal subgroup, chart and quotient permutation action.
In particular a two-thirds degree bound is sufficient and is stable under
multiplying the local degree by the actual number of blocks. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The actual scalar margin required by the existing complete-source
transfer, with no replacement classification premise. -/
structure PreE7SemisimpleMarginData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  chart : SemisimpleNormalChart E
  quotientDegree : ℕ
  quotientAction :
    (preE7NonPairAction w i ⧸ E) →* Equiv.Perm (Fin quotientDegree)
  quotientAction_injective : Function.Injective quotientAction
  quotientDegree_margin : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - (max 2 quotientDegree : ℕ)) / 8

attribute [instance] PreE7SemisimpleMarginData.E_normal

namespace PreE7SemisimpleMarginData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7SemisimpleMarginData w i)

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

/-- A uniform two-thirds bound leaves the exact fixed padding margin. -/
theorem margin_of_two_thirds {w v : ℕ} (hw : 5≤w) (hv : 3*v≤2*w) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - (max 2 v : ℕ)) / 8 := by
  have heven : (w : ℝ)≤(evenWidth w : ℝ)+1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hwR : (5 : ℝ)≤w := by exact_mod_cast hw
  have hvR : (3 : ℝ)*v≤2*w := by exact_mod_cast hv
  by_cases hv2 : v≤2
  · rw [max_eq_left hv2]
    unfold preE7CharacterRho
    norm_num
    linarith
  · rw [max_eq_right (by omega : 2≤v)]
    unfold preE7CharacterRho
    norm_num
    linarith

/-- The same original quotient comparator enters the existing complete
semisimple transfer whenever its faithful degree is at most two thirds of
its original ambient width. -/
noncomputable def ofTwoThirds
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (hw : 5≤w) (E : Subgroup (preE7NonPairAction w i)) [E.Normal]
    (chart : SemisimpleNormalChart E) (v : ℕ)
    (action : (preE7NonPairAction w i⧸E)→*Equiv.Perm (Fin v))
    (hinjective : Function.Injective action) (hv : 3*v≤2*w) :
    PreE7SemisimpleMarginData w i where
  width_lower := hw
  E := E
  E_normal := inferInstance
  chart := chart
  quotientDegree := v
  quotientAction := action
  quotientAction_injective := hinjective
  quotientDegree_margin := margin_of_two_thirds hw hv

end PreE7SemisimpleMarginData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
