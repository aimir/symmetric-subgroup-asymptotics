import SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer

/-!
# Uniform numerical retention for bounded carrier words

The physical half-degree of a word is its critical rank plus its noncritical
half-support.  A positive word of half-degree at most eight therefore retains
at least one quarter of that degree.  This is the numerical core needed for
each original orbit of size four, eight, or sixteen; route-specific work only
has to identify the word's half-degree with the original orbit half-size.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRetentionNumerics

open SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer
open SymmetricSubgroupAsymptotics.BinaryCarrierCellProfile
open SymmetricSubgroupAsymptotics.BinaryCarrierWordClosure

/-- Half the physical point degree occupied by one displayed mixture cell. -/
def cellHalfDegree : Kind → ℕ
  | .inl .c2 => 1
  | .inl .v4 => 2
  | .inl .d8 => 2
  | .inl .e8 => 4
  | .inr none => 2
  | .inr (some t) =>
      4 * SymmetricSubgroupAsymptotics.BinaryCarrierOriginalActions.factorScaleNat t

/-- The part of a displayed cell which remains in the noncritical retained
support.  Critical cells contribute to the critical rank instead. -/
def retainedCellHalfSupport : Kind → ℕ
  | .inl _ => 0
  | .inr none => 2
  | .inr (some t) =>
      4 * SymmetricSubgroupAsymptotics.BinaryCarrierOriginalActions.factorScaleNat t

/-- Reindex any additive cell weight through the canonical colour-fibre
enumeration.  This is the finite Fubini step which prevents a chosen route or
profile from becoming counted marking data. -/
theorem sum_cellWeight_eq_multiplicity
    {δ : Type*} [Fintype δ] (κ : δ → Type*) [∀ i, Fintype (κ i)]
    (color : Cell κ → Kind) (w : Kind → ℕ) :
    (∑ c : Cell κ, w (color c)) =
      ∑ g : Kind, multiplicity κ color g * w g := by
  calc
    _ = ∑ o : Σ g, Fin (multiplicity κ color g), w o.1 :=
      Fintype.sum_equiv (cellToOccurrence κ color)
        _ _ (fun c => by rw [cellToOccurrence_color])
    _ = ∑ g : Kind, ∑ _j : Fin (multiplicity κ color g), w g :=
      Fintype.sum_sigma _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      simp [Finset.sum_const]

/-- Retained support carried by the literal cells of one routed slot. -/
def slotRetainedHalfSupport (S : Slot) : ℕ :=
  ∑ j : S.Cells, retainedCellHalfSupport (S.color j)

/-- Physical half-degree carried by the literal cells of one routed slot. -/
def slotHalfDegree (S : Slot) : ℕ :=
  ∑ j : S.Cells, cellHalfDegree (S.color j)

private theorem criticalKind_univ :
    (Finset.univ : Finset CriticalActionKind) =
      {.c2, .v4, .d8, .e8} := by
  decide

private theorem critical_cellHalfDegree_sum
    {δ : Type*} [Fintype δ] (κ : δ → Type*) [∀ i, Fintype (κ i)]
    (color : Cell κ → Kind) :
    (∑ i : CriticalActionKind,
      multiplicity κ color (.inl i) * cellHalfDegree (.inl i)) =
      multiplicity κ color (.inl .c2) +
        2 * multiplicity κ color (.inl .v4) +
        2 * multiplicity κ color (.inl .d8) +
        4 * multiplicity κ color (.inl .e8) := by
  rw [criticalKind_univ]
  simp [cellHalfDegree]
  omega

private theorem noncritical_cellHalfDegree_sum
    {δ : Type*} [Fintype δ] (κ : δ → Type*) [∀ i, Fintype (κ i)]
    (color : Cell κ → Kind) :
    (∑ t : Option BinaryCarrierOriginalActions.Target,
      multiplicity κ color (.inr t) * cellHalfDegree (.inr t)) =
      2 * cyclicMultiplicity κ color + 4 * carrierScale κ color := by
  rw [Fintype.sum_option]
  unfold cyclicMultiplicity carrierScale BinaryCarrierOriginalActions.scale
  simp only [noncritical, cellHalfDegree]
  rw [Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro t ht
    ring

theorem multiplicity_retainedCellHalfSupport_sum
    {δ : Type*} [Fintype δ] (κ : δ → Type*) [∀ i, Fintype (κ i)]
    (color : Cell κ → Kind) :
    (∑ g : Kind, multiplicity κ color g * retainedCellHalfSupport g) =
      2 * cyclicMultiplicity κ color + 4 * carrierScale κ color := by
  rw [Fintype.sum_sum_type]
  simp only [retainedCellHalfSupport, Nat.mul_zero, Finset.sum_const_zero,
    zero_add]
  exact noncritical_cellHalfDegree_sum κ color

theorem multiplicity_cellHalfDegree_sum
    {δ : Type*} [Fintype δ] (κ : δ → Type*) [∀ i, Fintype (κ i)]
    (color : Cell κ → Kind) :
    (∑ g : Kind, multiplicity κ color g * cellHalfDegree g) =
      criticalRank κ color + 2 * cyclicMultiplicity κ color +
        4 * carrierScale κ color := by
  rw [Fintype.sum_sum_type, critical_cellHalfDegree_sum,
    noncritical_cellHalfDegree_sum]
  unfold criticalRank critical CriticalProfile.rank
  ring

theorem cellWeight_sum_eq_slot_sum
    {δ : Type*} [Fintype δ] (slot : δ → Slot) (w : Kind → ℕ) :
    (∑ c : Σ i, cells slot i, w (colors slot c)) =
      ∑ i, ∑ j : (slot i).Cells, w ((slot i).color j) := by
  exact Fintype.sum_sigma _

/-- The canonical multiplicity formula for the noncritical parameter is
literally the sum of the retained support of all displayed slot cells. -/
theorem wordSupport_eq_sum_retainedHalfSupport
    {δ : Type*} [Fintype δ] [DecidableEq δ] (slot : δ → Slot) :
    wordSupport slot = ∑ i, slotRetainedHalfSupport (slot i) := by
  change wordSupport slot =
    ∑ i, ∑ j : (slot i).Cells, retainedCellHalfSupport ((slot i).color j)
  rw [← cellWeight_sum_eq_slot_sum slot retainedCellHalfSupport]
  rw [sum_cellWeight_eq_multiplicity (cells slot) (colors slot)
    retainedCellHalfSupport]
  exact (multiplicity_retainedCellHalfSupport_sum
    (cells slot) (colors slot)).symm

/-- The exact physical half-degree of the word is the sum of the literal
half-degrees of its routed slots. -/
theorem wordParameter_eq_sum_halfDegree
    {δ : Type*} [Fintype δ] [DecidableEq δ] (slot : δ → Slot) :
    wordParameter slot = ∑ i, slotHalfDegree (slot i) := by
  change wordParameter slot =
    ∑ i, ∑ j : (slot i).Cells, cellHalfDegree ((slot i).color j)
  rw [← cellWeight_sum_eq_slot_sum slot cellHalfDegree]
  rw [sum_cellWeight_eq_multiplicity (cells slot) (colors slot)
    cellHalfDegree]
  exact (multiplicity_cellHalfDegree_sum
    (cells slot) (colors slot)).symm

/-- Assemble the global retained-bin certificate from literal per-slot old
support bounds.  The retained function is canonical: it is the sum of the
fixed weights of the cells displayed by that slot. -/
def Retention.ofSlotSupport
    {δ : Type*} [Fintype δ] [DecidableEq δ]
    (slot : δ → Slot) {Cold : ℕ} (oldSupport : δ → ℕ)
    (old_sum : ∑ i, oldSupport i = Cold)
    (retained_le_old : ∀ i,
      slotRetainedHalfSupport (slot i) ≤ oldSupport i)
    (old_le_four_retained : ∀ i,
      oldSupport i ≤ 4 * slotRetainedHalfSupport (slot i)) :
    Retention slot Cold where
  oldSupport := oldSupport
  retainedSupport := fun i => slotRetainedHalfSupport (slot i)
  old_sum := old_sum
  retained_sum := (wordSupport_eq_sum_retainedHalfSupport slot).symm
  retained_le_old := retained_le_old
  old_le_four_retained := old_le_four_retained

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (slot : ι → Slot)

/-- The retained noncritical half-support is part of the complete physical
half-degree of the word. -/
theorem wordSupport_le_wordParameter :
    wordSupport slot ≤ wordParameter slot := by
  unfold wordSupport wordParameter BinaryCarrierWordClosure.parameter
  omega

/-- A positive word of half-degree at most eight retains at least one quarter
of its half-degree. -/
theorem wordParameter_le_four_wordSupport_of_noncritical
    (hnoncritical : ∃ c : Σ i, cells slot i, ∃ t,
      colors slot c = .inr t)
    (hparameter : wordParameter slot ≤ 8) :
    wordParameter slot ≤ 4 * wordSupport slot := by
  have hpositive : 0 < wordSupport slot :=
    support_pos_of_noncritical (cells slot) (colors slot) hnoncritical
  unfold wordSupport at hpositive ⊢
  omega

end SymmetricSubgroupAsymptotics.BinaryCarrierRetentionNumerics

end
