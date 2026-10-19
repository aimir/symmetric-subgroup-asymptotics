import SymmetricSubgroupAsymptotics.MarkedC4ActualLogPeelingAndSelfCost
import Mathlib.Data.List.NodupEquivFin

/-! Selected original-factor orders and literal prefix supports. The
selection has no repeated or missing physical labels. Ordered prefix kernels
are identified with actual zero-outside subgroups in the original product. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualSelectedOrderPrefix
open ActualTableauPeeling

variable {I : Type} [DecidableEq I]

theorem Plan.nodup {ρ : I → Finset I → ℝ} {S : Finset I} {l : List I}
    (h : Plan ρ S l) : l.Nodup := by
  induction h with
  | nil => simp
  | @cons S i l hi hmax htail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro himem
    have hm : i∈l.toFinset := List.mem_toFinset.mpr himem
    rw [htail.labels] at hm
    exact (Finset.mem_erase.mp hm).1 rfl

/-- At every actual residual tail, its head satisfies the constructed
maximum comparison. This retains all original factor labels. -/
theorem Plan.tail_maximum {ρ : I → Finset I → ℝ} {S : Finset I} {l : List I}
    (h : Plan ρ S l) (k : ℕ) (hk : k<l.length) :
    ∀ j∈(l.drop k).toFinset,
      ρ j (l.drop k).toFinset≤ρ (l[k]'hk) (l.drop k).toFinset := by
  induction h generalizing k with
  | nil => simp at hk
  | @cons S i l hi hmax htail ih =>
    cases k with
    | zero =>
      have hs : (i::l).toFinset=S := (Plan.cons hi hmax htail).labels
      simpa only [List.drop_zero,List.getElem_cons_zero,hs] using hmax
    | succ k =>
      have hkt : k<l.length := by
        simp only [List.length_cons] at hk
        omega
      simpa only [List.drop_succ_cons,List.getElem_cons_succ] using ih k hkt

section Complete
variable [Fintype I]

/-- Peeling head-first is reversed for the physical prefix order. -/
def reverseOrder {ρ : I → Finset I → ℝ} {l : List I}
    (h : Plan ρ Finset.univ l) : Fin l.length ≃ I :=
  (finCongr (List.length_reverse (as := l)).symm).trans
    (List.Nodup.getEquivOfForallMemList l.reverse
      (List.nodup_reverse.mpr (ActualSelectedOrderPrefix.Plan.nodup h)) (by
      intro i
      apply List.mem_reverse.mpr
      apply List.mem_toFinset.mp
      rw [h.labels]
      exact Finset.mem_univ i))

variable {t : ℕ} (e : Fin t ≃ I)
  (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))

def initialLabels (m : ℕ) : Finset I :=
  Finset.univ.filter (fun i => (e.symm i).val < m)

def orderedPrefix (m : ℕ) : Subgroup H :=
  ⨅ k : {k : Fin t // m ≤ k.val},(coordinate F H (e k.val)).ker

theorem mem_orderedPrefix (m : ℕ) (h : H) :
    h∈orderedPrefix e F H m ↔ ∀ k : Fin t,m ≤ k.val → h.val (e k)=1 := by
  simp only [orderedPrefix,Subgroup.mem_iInf,MonoidHom.mem_ker,Subtype.forall,coordinate]
  rfl

/-- Literal support transport: the same original H and its original
coordinates are retained through the selected physical order. -/
theorem orderedPrefix_eq_zeroOutside (m : ℕ) :
    orderedPrefix e F H m=zeroOutside F H (initialLabels e m) := by
  ext h
  rw [mem_orderedPrefix]
  simp only [zeroOutside,Subgroup.mem_iInf,MonoidHom.mem_ker,Subtype.forall]
  constructor
  · intro hh j hj
    have hnot : ¬ ((e.symm j).val < m) := by
      intro hx
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hx⟩)
    have hx := hh (e.symm j) (Nat.le_of_not_gt hnot)
    rw [e.apply_symm_apply] at hx
    change h.val j=1
    exact hx
  · intro hh k hk
    apply hh (e k)
    intro hmem
    have hm := (Finset.mem_filter.mp hmem).2
    rw [e.symm_apply_apply] at hm
    omega

/-- The ordered coordinate layer is precisely the actual residual-image
entry used by the density maximization, with no abstract replacement group. -/
theorem ordered_entry (m : ℕ) (j : Fin t) :
    (orderedPrefix e F H m).map (coordinate F H (e j))=
      entry F H (initialLabels e m) (e j) := by
  rw [orderedPrefix_eq_zeroOutside]
  rfl

end Complete
end SymmetricSubgroupAsymptotics.MarkedC4.ActualSelectedOrderPrefix
