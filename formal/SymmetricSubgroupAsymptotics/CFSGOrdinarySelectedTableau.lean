import SymmetricSubgroupAsymptotics.CFSGOrdinaryTableauCount
import SymmetricSubgroupAsymptotics.MarkedC4ActualSelectedTableauPacket

/-! Bind the ordinary prime-independent tableau estimate to the greedy
physical order constructed from one ACTUAL nilpotent subdirect source.
No selected density, independent model source, or count estimate is a premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinarySelectedTableau
open MarkedC4 ActualTableauPeeling ActualSelectedOrderPrefix ActualSelectedDensityComparisons
open ActualOrderedSubdirectTransport ActualSelectedTableauPacket

variable {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (H : Subgroup (∀ i,F i)) (weight : I → ℕ)
    {l : List I}
    (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l)

/-- Original factor order bounds control the same selected real-log
densities, for arbitrary prime groups and arbitrary finite nilpotent groups. -/
theorem selectedDensity_le (C : ℝ) (hw : ∀ i,0 < weight i)
    (horder : ∀ i,Real.logb 2 (Nat.card (F i)) ≤ C*weight i) (j : Fin l.length) :
    selectedDensity F H weight h j ≤ C := by
  let U := ActualTableauPeeling.entry F H
    (initialLabels (reverseOrder h) (j.val+1)) (reverseOrder h j)
  have hu : Real.logb 2 (Nat.card U) ≤ C*weight (reverseOrder h j) := by
    apply (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (show (0 : ℝ) < Nat.card U by exact_mod_cast Nat.card_pos) _).trans (horder _)
    exact_mod_cast Nat.card_le_card_of_injective U.subtype Subtype.val_injective
  unfold selectedDensity ActualLogPeelingAndSelfCost.density
  apply (div_le_iff₀ (show (0 : ℝ) < weight (reverseOrder h j) by exact_mod_cast hw _)).mpr
  simpa only [mul_comm] using hu

/-- A true actual selected-tableau count from order and uniform normal
rank bounds on the original factors. It applies in particular to the
odd-prime route without any binary ceiling-log identity. -/
theorem selected_tableau_card_le
    (hfull : ∀ i,Function.Surjective (ActualTableauPeeling.coordinate F H i))
    [Group.IsNilpotent H] (C d B : ℝ) (hC : 0 < C) (hd : 0 ≤ d)
    (hw : ∀ i,0 < weight i)
    (horder : ∀ i,Real.logb 2 (Nat.card (F i)) ≤ C*weight i)
    (hbounded : ∀ i,Real.logb 2 (Nat.card (F i)) ≤ B)
    (hnormal : ∀ i (N : Subgroup (F i)) [N.Normal],
      (normalGen N : ℝ) ≤ d*weight i) :
    (Nat.card (ActualTableauRowIncidence.TableauFamily
      (orderedFactors F H weight h) (diagonals F H weight h) (tableau F H weight h)) : ℝ) ≤ 
      (2 : ℝ)^(C*d*(∑ i : I,(weight i : ℝ))^2/4+(l.length : ℝ)*B^2) := by
  let c : Fin l.length → ℝ := fun i => selectedDensity F H weight h i/C
  let n : Fin l.length → ℝ := fun i => weight (reverseOrder h i)
  have hcancel (i : Fin l.length) : C*c i=selectedDensity F H weight h i := by
    dsimp [c]
    field_simp [ne_of_gt hC]
  have hmem := member F H weight h hfull
  have hbound := CFSGOrdinaryTableauCount.card_le_quadratic
    (orderedFactors F H weight h) (diagonals F H weight h) (tableau F H weight h)
    hmem c n C d B hC.le hd
    (fun i => div_nonneg (ActualBinaryLogDensityBinding.selectedDensity_nonneg F H weight h i) hC.le)
    (fun i => (div_le_one hC).mpr (selectedDensity_le F H weight h C hw horder i))
    (fun i => Nat.cast_nonneg _)
    (fun i j hij => div_le_div_of_nonneg_right (selectedDensity_mono F H weight h hij) hC.le)
    (by
      intro i j hji
      rw [hcancel]
      exact entry_bound F H weight h hw i j hji)
    (by
      intro i
      rw [hcancel]
      exact diagonal_log F H weight h hw i)
    (by
      intro i
      letI : (diagonals F H weight h i).Normal := by
        rw [show diagonals F H weight h i=
          ActualSubdirectFiltration.diagonal (orderedFactors F H weight h)
            (orderedSource F H weight h) i from (diagonal_eq_entry (reverseOrder h) F H i).symm]
        exact ActualSubdirectFiltration.diagonalNormal _ _
          (subdirect (reverseOrder h) F H hfull) i
      exact hnormal (reverseOrder h i) (diagonals F H weight h i))
    (fun i => hbounded (reverseOrder h i))
  have hn : (∑ i : Fin l.length,n i)=∑ i : I,(weight i : ℝ) := by
    exact (reverseOrder h).sum_comp (fun i : I => (weight i : ℝ))
  rw [hn] at hbound
  exact hbound

end SymmetricSubgroupAsymptotics.CFSGOrdinarySelectedTableau
