import SymmetricSubgroupAsymptotics.MarkedC4ActualSelectedDensityComparisons
import Mathlib.Data.Nat.Log

/-! Coherent actual binary density binding. Ceiling and real logarithms
agree on actual finite binary groups, so one selected density packet supplies
BOTH the entropy identity and the simultaneous source-column order identity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryLogDensityBinding
open ActualTableauPeeling ActualSelectedOrderPrefix ActualSelectedDensityComparisons

theorem clog_card_eq_real_log {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G) :
    (Nat.clog 2 (Nat.card G) : ℝ)=Real.logb 2 (Nat.card G) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a,ha⟩ := hG.exists_card_eq
  rw [ha,Nat.clog_pow 2 a (by norm_num),Nat.cast_pow,Nat.cast_ofNat,
    Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one]

variable {I : Type} [Fintype I] [DecidableEq I]
  (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i)) (weight : I → ℕ)

/-- The column packet and exact incidence packet use the SAME actual
selected diagonal entry, not independently maximized abstract sources. -/
theorem selected_diagonal_clog_eq {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l)
    (hw : ∀ j,0<weight j) (hF : ∀ j,IsPGroup 2 (F j)) (i : Fin l.length) :
    (Nat.clog 2 (Nat.card (entry F H
      (initialLabels (reverseOrder h) (i.val+1)) (reverseOrder h i))) : ℝ)=
        selectedDensity F H weight h i*(weight (reverseOrder h i) : ℝ) := by
  rw [clog_card_eq_real_log ((hF (reverseOrder h i)).to_subgroup _)]
  exact diagonal_log_eq_selected F H weight h hw i

theorem selectedDensity_nonneg {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l)
    (i : Fin l.length) : 0≤selectedDensity F H weight h i := by
  unfold selectedDensity ActualLogPeelingAndSelfCost.density
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Real.logb_nonneg (by norm_num : (1 : ℝ)<2)
  exact_mod_cast (Nat.succ_le_iff.mpr (Nat.card_pos (α := entry F H
    (initialLabels (reverseOrder h) (i.val+1)) (reverseOrder h i))))

/-- A local physical order bound is enough for the constructed selected
density to lie in [0,1]. It is a group-order condition, not a count input. -/
theorem selectedDensity_le_one {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l)
    (hw : ∀ j,0<weight j) (hcard : ∀ j,Nat.card (F j)≤2^weight j)
    (i : Fin l.length) : selectedDensity F H weight h i≤1 := by
  let U := entry F H (initialLabels (reverseOrder h) (i.val+1)) (reverseOrder h i)
  have hu : Nat.card U≤2^weight (reverseOrder h i) :=
    (Nat.card_le_card_of_injective U.subtype Subtype.val_injective).trans (hcard _)
  have hlog : Real.logb 2 (Nat.card U)≤(weight (reverseOrder h i) : ℝ) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
      (show (0 : ℝ)<Nat.card U by exact_mod_cast Nat.card_pos)).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast hu
  unfold selectedDensity ActualLogPeelingAndSelfCost.density
  apply (div_le_iff₀ (show (0 : ℝ)<weight (reverseOrder h i) by
    exact_mod_cast hw _)).mpr
  simpa only [one_mul] using hlog

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryLogDensityBinding
