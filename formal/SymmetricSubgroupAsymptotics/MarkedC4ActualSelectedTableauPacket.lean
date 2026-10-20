import SymmetricSubgroupAsymptotics.MarkedC4ActualOrderedSubdirectTransport
import SymmetricSubgroupAsymptotics.MarkedC4ActualBinaryLogDensityBinding
import SymmetricSubgroupAsymptotics.MarkedC4ActualCorrelatedTableauHall

/-! A selected tableau packet constructed from ONE actual subgroup.
Every row, diagonal and density below uses its same greedy physical order. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSelectedTableauPacket
open ActualTableauPeeling ActualSelectedOrderPrefix ActualSelectedDensityComparisons
open ActualOrderedSubdirectTransport

variable {I : Type} [Fintype I] [DecidableEq I]
  (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))

theorem entry_transport {t : ℕ} (e : Fin t ≃ I) (i j : Fin t) :
    (ActualSubdirectFiltration.«prefix» (Factors e F) (image e F H) (i.val+1)).map
      (ActualSubdirectFiltration.coordinate (Factors e F) (image e F H) j)=
      entry F H (initialLabels e (i.val+1)) (e j) := by
  rw [← prefix_map,Subgroup.map_map]
  have hc :
      (ActualSubdirectFiltration.coordinate (Factors e F) (image e F H) j).comp
        (sourceEquiv e F H).toMonoidHom=coordinate F H (e j) := by
    ext x
    rfl
  rw [hc,ordered_entry]

variable (weight : I → ℕ) {l : List I}
  (h : Plan (ActualLogPeelingAndSelfCost.density F H weight) Finset.univ l)

abbrev orderedFactors := Factors (reverseOrder h) F
abbrev orderedSource := image (reverseOrder h) F H
def diagonals (i : Fin l.length) : Subgroup (orderedFactors F H weight h i) :=
  entry F H (initialLabels (reverseOrder h) (i.val+1)) (reverseOrder h i)
def tableau (i j : Fin l.length) : Subgroup (orderedFactors F H weight h j) :=
  entry F H (initialLabels (reverseOrder h) (i.val+1)) (reverseOrder h j)

def member (hfull : ∀ i,Function.Surjective (coordinate F H i)) [Group.IsNilpotent H] :
    ActualTableauRowIncidence.TableauFamily (orderedFactors F H weight h)
      (diagonals F H weight h) (tableau F H weight h) := by
  letI : Group.IsNilpotent (orderedSource F H weight h) :=
    Group.nilpotent_of_mulEquiv (sourceEquiv (reverseOrder h) F H)
  refine ⟨⟨orderedSource F H weight h,?_,inferInstance,?_⟩,?_⟩
  · exact subdirect (reverseOrder h) F H hfull
  · intro i
    exact diagonal_eq_entry (reverseOrder h) F H i
  · intro i j
    exact entry_transport F H (reverseOrder h) i j

theorem entry_bound (hw : ∀ i,0<weight i) (i j : Fin l.length) (hji : j.val ≤ i.val) :
    Real.logb 2 (Nat.card (tableau F H weight h i j))≤
      selectedDensity F H weight h i*(weight (reverseOrder h j) : ℝ) :=
  entry_log_le_selected F H weight h hw i j hji

theorem diagonal_log (hw : ∀ i,0<weight i) (i : Fin l.length) :
    Real.logb 2 (Nat.card (diagonals F H weight h i))=
      selectedDensity F H weight h i*(weight (reverseOrder h i) : ℝ) :=
  diagonal_log_eq_selected F H weight h hw i

theorem diagonal_clog (hw : ∀ i,0<weight i) (hbinary : ∀ i,IsPGroup 2 (F i))
    (i : Fin l.length) :
    (Nat.clog 2 (Nat.card (diagonals F H weight h i)) : ℝ)=
      selectedDensity F H weight h i*(weight (reverseOrder h i) : ℝ) :=
  ActualBinaryLogDensityBinding.selected_diagonal_clog_eq F H weight h hw hbinary i

def weightAt (m : ℕ) : ℝ :=
  if hm : m<l.length then (weight (reverseOrder h ⟨m,hm⟩) : ℝ) else 0
def densityAt (m : ℕ) : ℝ :=
  if hm : m<l.length then selectedDensity F H weight h ⟨m,hm⟩ else 0

local instance : Fintype (ActualTableauRowIncidence.TableauFamily
    (orderedFactors F H weight h) (diagonals F H weight h) (tableau F H weight h)) :=
  Fintype.ofFinite _

/-- Actual Case-I Hall sum for the tableau selected from an arbitrary
actual subgroup. No ordered-density packet or enumeration bound is a premise. -/
theorem selected_hall_sum_le
    (hfull : ∀ i,Function.Surjective (coordinate F H i)) [Group.IsNilpotent H]
    (hw : ∀ i,0<weight i) (hbinary : ∀ i,IsPGroup 2 (F i))
    (hcard : ∀ i,Nat.card (F i)≤2^weight i)
    (hquarter : ∀ (i : I) (V : Subgroup (F i)),V.Normal →
      (normalGen V : ℝ)≤(weight i : ℝ)/4)
    (m r : ℕ) (A : Type) [CommGroup A] [Finite A]
    (hA : HasExp2 A (2+m)) {a B : ℝ} (ha : 0≤a)
    (hAcard : (Nat.card A : ℝ)≤(2 : ℝ)^(a/2))
    (hlog : ∀ i,Real.logb 2 (Nat.card (F i))≤B) :
    (∑ E : ActualTableauRowIncidence.TableauFamily (orderedFactors F H weight h)
        (diagonals F H weight h) (tableau F H weight h),
      (Nat.card (AbelianProductGraphClassification.FullSecond
        (A × Multiplicative (Fin r → ZMod 4)) E.val.val) : ℝ))≤
      ((∏ k ∈ Finset.range (2+m),
        ((col (A × Multiplicative (Fin r → ZMod 4)) k : ℝ)+1))*4^(2+m))*
        (2 : ℝ)^(markedF (a+prefixWeight (weightAt F H weight h) l.length) r+
          (l.length : ℝ)*B^2) := by
  apply ActualCorrelatedTableauHall.fullSecond_sum_le
    (orderedFactors F H weight h) (diagonals F H weight h) (tableau F H weight h)
    (member F H weight h hfull) (densityAt F H weight h) (weightAt F H weight h)
    m r A hA ha hAcard
  · intro k hk
    simp only [weightAt,dif_pos hk]
    exact Nat.cast_nonneg _
  · intro k hk
    simpa only [densityAt,dif_pos hk] using
      ActualBinaryLogDensityBinding.selectedDensity_nonneg F H weight h ⟨k,hk⟩
  · intro k hk
    simpa only [densityAt,dif_pos hk] using
      ActualBinaryLogDensityBinding.selectedDensity_le_one F H weight h hw hcard ⟨k,hk⟩
  · intro j k hjk hk
    have hj : j<l.length := lt_of_le_of_lt hjk hk
    simp only [densityAt,dif_pos hj,dif_pos hk]
    exact selectedDensity_mono F H weight h (show (⟨j,hj⟩ : Fin l.length)≤⟨k,hk⟩ from hjk)
  · intro i j hji
    simpa only [densityAt,weightAt,dif_pos i.isLt,dif_pos j.isLt] using
      entry_bound F H weight h hw i j hji
  · intro i
    simpa only [densityAt,weightAt,dif_pos i.isLt] using diagonal_log F H weight h hw i
  · intro i
    simpa only [densityAt,weightAt,dif_pos i.isLt] using
      diagonal_clog F H weight h hw hbinary i
  · intro i
    simp only [weightAt,dif_pos i.isLt]
    apply hquarter (reverseOrder h i)
    rw [show diagonals F H weight h i=
      ActualSubdirectFiltration.diagonal (orderedFactors F H weight h)
        (orderedSource F H weight h) i from (diagonal_eq_entry (reverseOrder h) F H i).symm]
    exact ActualSubdirectFiltration.diagonalNormal _ _ (subdirect (reverseOrder h) F H hfull) i
  · intro i
    exact hlog (reverseOrder h i)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualSelectedTableauPacket
