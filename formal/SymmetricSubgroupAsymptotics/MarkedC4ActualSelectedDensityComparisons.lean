import SymmetricSubgroupAsymptotics.MarkedC4ActualSelectedOrderPrefix
import Mathlib.Data.List.Basic

/-! The reverse selected physical order really has the initial sets used
by the literal prefix tableau. Consequently its local entry comparisons and
monotone diagonal densities are constructed from the actual peeling plan. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSelectedDensityComparisons
open ActualTableauPeeling ActualSelectedOrderPrefix

variable {I : Type} [Fintype I] [DecidableEq I]

theorem reverseOrder_symm_val {ρ : I → Finset I → ℝ} {l : List I}
    (h : Plan ρ Finset.univ l) (j : I) :
    ((reverseOrder h).symm j).val=l.reverse.idxOf j := rfl

theorem reverseOrder_apply {ρ : I → Finset I → ℝ} {l : List I}
    (h : Plan ρ Finset.univ l) (i : Fin l.length) :
    reverseOrder h i=l.reverse[i.val]'(by simpa only [List.length_reverse] using i.isLt) := rfl

theorem initialLabels_eq_take {ρ : I → Finset I → ℝ} {l : List I}
    (h : Plan ρ Finset.univ l) (m : ℕ) :
    initialLabels (reverseOrder h) m=(l.reverse.take m).toFinset := by
  ext j
  have hj : j∈l.reverse := by
    apply List.mem_reverse.mpr
    apply List.mem_toFinset.mp
    rw [h.labels]
    exact Finset.mem_univ j
  simp only [initialLabels,Finset.mem_filter,Finset.mem_univ,true_and,
    reverseOrder_symm_val,List.mem_toFinset,List.mem_take_iff_idxOf_lt hj]

/-- The selected initial set is EXACTLY its original residual tail. -/
theorem initialLabels_eq_tail {ρ : I → Finset I → ℝ} {l : List I}
    (h : Plan ρ Finset.univ l) (m : ℕ) :
    initialLabels (reverseOrder h) m=(l.drop (l.length-m)).toFinset := by
  rw [initialLabels_eq_take,List.take_reverse,List.toFinset_reverse]

theorem selected_maximum {ρ : I → Finset I → ℝ} {l : List I}
    (h : Plan ρ Finset.univ l) (i : Fin l.length) :
    ∀ j∈initialLabels (reverseOrder h) (i.val+1),
      ρ j (initialLabels (reverseOrder h) (i.val+1))≤
        ρ (reverseOrder h i) (initialLabels (reverseOrder h) (i.val+1)) := by
  have hk : l.length-1-i.val<l.length := by omega
  have hm := ActualSelectedOrderPrefix.Plan.tail_maximum h (l.length-1-i.val) hk
  have he : reverseOrder h i=l[l.length-1-i.val]'hk := by
    exact (reverseOrder_apply h i).trans
      (List.getElem_reverse (l := l) (i := i.val)
        (by simpa only [List.length_reverse] using i.isLt))
  have hn : l.length-(i.val+1)=l.length-1-i.val := by omega
  rw [initialLabels_eq_tail,hn,he]
  exact hm

variable (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i)) (weight : I → ℕ)

def selectedDensity {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l)
    (i : Fin l.length) : ℝ :=
  ActualLogPeelingAndSelfCost.density F H weight (reverseOrder h i)
    (initialLabels (reverseOrder h) (i.val+1))

theorem initialLabels_mono {t : ℕ} (e : Fin t ≃ I) {m n : ℕ} (hmn : m≤n) :
    initialLabels e m⊆initialLabels e n := by
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ((Finset.mem_filter.mp hj).2).trans_le hmn⟩

/-- These are the actual local order comparisons required by the sharp
tableau entropy theorem, now derived from the selected physical order. -/
theorem entry_log_le_selected {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l)
    (hw : ∀ j,0<weight j) (i j : Fin l.length) (hji : j.val ≤ i.val) :
    Real.logb 2 (Nat.card (entry F H
      (initialLabels (reverseOrder h) (i.val+1)) (reverseOrder h j)))≤
        selectedDensity F H weight h i*(weight (reverseOrder h j) : ℝ) := by
  have hj : reverseOrder h j∈initialLabels (reverseOrder h) (i.val+1) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [(reverseOrder h).symm_apply_apply]
    omega
  have hm := selected_maximum h i (reverseOrder h j) hj
  exact (div_le_iff₀ (show (0 : ℝ)<weight (reverseOrder h j) by
    exact_mod_cast hw (reverseOrder h j))).mp hm

/-- Diagonal log-density identity for the SAME actual residual entry. -/
theorem diagonal_log_eq_selected {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l)
    (hw : ∀ j,0<weight j) (i : Fin l.length) :
    Real.logb 2 (Nat.card (entry F H
      (initialLabels (reverseOrder h) (i.val+1)) (reverseOrder h i)))=
        selectedDensity F H weight h i*(weight (reverseOrder h i) : ℝ) := by
  unfold selectedDensity ActualLogPeelingAndSelfCost.density
  exact (div_mul_cancel₀ _ (show (weight (reverseOrder h i) : ℝ)≠0 by
    exact_mod_cast (hw (reverseOrder h i)).ne')).symm

/-- The selected actual diagonal densities are monotone in the physical
prefix order; this is not supplied as an ordering hypothesis. -/
theorem selectedDensity_mono {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l) :
    Monotone (selectedDensity F H weight h) := by
  intro j i hji
  have hval : j.val ≤ i.val := hji
  have hj : reverseOrder h j∈initialLabels (reverseOrder h) (i.val+1) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [(reverseOrder h).symm_apply_apply]
    omega
  exact (ActualLogPeelingAndSelfCost.density_mono F H weight (reverseOrder h j)
    (initialLabels_mono (reverseOrder h) (by omega))).trans (selected_maximum h i _ hj)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualSelectedDensityComparisons
