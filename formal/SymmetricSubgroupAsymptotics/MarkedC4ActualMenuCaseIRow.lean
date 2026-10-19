import SymmetricSubgroupAsymptotics.MarkedC4ActualOccupiedMenuCover

/-! The Case-I optimized row for every occupied finite menu. Its density
packet is constructed from the actual source selecting that menu. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMenuCaseIRow
open ActualWordMenuPartition ActualSelectedDensityComparisons ActualSelectedOrderPrefix

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (weight : Fin t → ℕ) (H : Family F)

def index (i : Fin t) : Fin (selectedList F weight H).length :=
  finCongr (selectedLength F weight H).symm i
def density (i : Fin t) : ℝ := selectedDensity F H.val weight (selectedPlan F weight H)
  (index F weight H i)
def cAt (m : ℕ) : ℝ := if hm : m<t then density F weight H ⟨m,hm⟩ else 0
def nAt (q : Menu F) (m : ℕ) : ℝ :=
  if hm : m<t then (weight (q.1 ⟨m,hm⟩) : ℝ) else 0

theorem tableau_eq_entry (i j : Fin t) :
    menuTableau F (key F weight H) i j=ActualTableauPeeling.entry F H.val
      (initialLabels (reverseOrder (selectedPlan F weight H)) (i.val+1))
      (reverseOrder (selectedPlan F weight H) (index F weight H j)) := by
  change (orderedPrefix (selectedOrder F weight H) F H.val (i.val+1)).map
    (ActualTableauPeeling.coordinate F H.val (selectedOrder F weight H j))=_
  rw [ordered_entry]
  rfl

theorem entry_log_bound (hw : ∀ i,0<weight i) (i j : Fin t) (hji : j.val ≤ i.val) :
    Real.logb 2 (Nat.card (menuTableau F (key F weight H) i j))≤
      density F weight H i*(weight ((key F weight H).1 j) : ℝ) := by
  rw [tableau_eq_entry]
  exact entry_log_le_selected F H.val weight (selectedPlan F weight H) hw
    (index F weight H i) (index F weight H j) hji

theorem diagonal_log (hw : ∀ i,0<weight i) (i : Fin t) :
    Real.logb 2 (Nat.card (menuDiagonal F (key F weight H) i))=
      density F weight H i*(weight ((key F weight H).1 i) : ℝ) := by
  change Real.logb 2 (Nat.card (menuTableau F (key F weight H) i i))=_
  rw [tableau_eq_entry]
  exact diagonal_log_eq_selected F H.val weight (selectedPlan F weight H) hw
    (index F weight H i)

theorem diagonal_clog (hw : ∀ i,0<weight i) (hbinary : ∀ i,IsPGroup 2 (F i)) (i : Fin t) :
    (Nat.clog 2 (Nat.card (menuDiagonal F (key F weight H) i)) : ℝ)=
      density F weight H i*(weight ((key F weight H).1 i) : ℝ) := by
  change (Nat.clog 2 (Nat.card (menuTableau F (key F weight H) i i)) : ℝ)=_
  rw [tableau_eq_entry]
  exact ActualBinaryLogDensityBinding.selected_diagonal_clog_eq F H.val weight
    (selectedPlan F weight H) hw hbinary (index F weight H i)

local instance : Fintype (MenuFamily F (key F weight H)) := Fintype.ofFinite _

/-- A literal occupied menu receives the sharp correlated Hall bound.
The hypotheses are physical binary order and nonexcess conditions only. -/
theorem menu_hall_sum_le
    (hw : ∀ i,0<weight i) (hbinary : ∀ i,IsPGroup 2 (F i))
    (hcard : ∀ i,Nat.card (F i)≤2^weight i)
    (hquarter : ∀ (i : Fin t) (V : Subgroup (F i)),V.Normal →
      (normalGen V : ℝ)≤(weight i : ℝ)/4)
    (m r : ℕ) (A : Type) [CommGroup A] [Finite A]
    (hA : HasExp2 A (2+m)) {a B : ℝ} (ha : 0≤a)
    (hAcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2))
    (hlog : ∀ i,Real.logb 2 (Nat.card (F i))≤B) :
    (∑ U : MenuFamily F (key F weight H),
      (Nat.card (AbelianProductGraphClassification.FullSecond
        (A × Multiplicative (Fin r → ZMod 4)) U.val.val) : ℝ))≤
      ((∏ k ∈ Finset.range (2+m),
        ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m))*
        (2 : ℝ)^(markedF (a+prefixWeight (nAt F weight (key F weight H)) t) r+
          (t : ℝ)*B^2) := by
  apply ActualCorrelatedTableauHall.fullSecond_sum_le
    (menuFactors F (key F weight H)) (menuDiagonal F (key F weight H))
    (menuTableau F (key F weight H)) (toMenu F weight H)
    (cAt F weight H) (nAt F weight (key F weight H)) m r A hA ha hAcard
  · intro k hk
    simp only [nAt,dif_pos hk]
    exact Nat.cast_nonneg _
  · intro k hk
    simpa only [cAt,dif_pos hk,density] using
      ActualBinaryLogDensityBinding.selectedDensity_nonneg F H.val weight
        (selectedPlan F weight H) (index F weight H ⟨k,hk⟩)
  · intro k hk
    simpa only [cAt,dif_pos hk,density] using
      ActualBinaryLogDensityBinding.selectedDensity_le_one F H.val weight
        (selectedPlan F weight H) hw hcard (index F weight H ⟨k,hk⟩)
  · intro j k hjk hk
    have hj : j<t := lt_of_le_of_lt hjk hk
    simp only [cAt,dif_pos hj,dif_pos hk,density]
    exact selectedDensity_mono F H.val weight (selectedPlan F weight H) hjk
  · intro i j hji
    simpa only [cAt,nAt,dif_pos i.isLt,dif_pos j.isLt] using
      entry_log_bound F weight H hw i j hji
  · intro i
    simpa only [cAt,nAt,dif_pos i.isLt] using diagonal_log F weight H hw i
  · intro i
    simpa only [cAt,nAt,dif_pos i.isLt] using diagonal_clog F weight H hw hbinary i
  · intro i
    simp only [nAt,dif_pos i.isLt]
    apply hquarter ((key F weight H).1 i)
    rw [← (toMenu F weight H).val.property.2.2 i]
    exact ActualSubdirectFiltration.diagonalNormal _ _ (toMenu F weight H).val.property.1 i
  · intro i
    exact hlog ((key F weight H).1 i)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMenuCaseIRow
