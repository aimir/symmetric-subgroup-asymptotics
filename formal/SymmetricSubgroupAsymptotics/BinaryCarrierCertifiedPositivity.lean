import SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalCertifiedWord

/-!
# Recovering positive cells from certified retained support

The numerical certificate already forces a noncritical physical cell whenever
its old support is positive.  This avoids carrying a second positivity mark
through the canonical word.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedPositivity

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalCertifiedWord
open BinaryCarrierCertifiedRetention
open BinaryCarrierRetentionNumerics
open BinaryDegreeEightPhysicalAnalyticClosure

/-- Positive retained half-support can only come from a displayed
noncritical cell. -/
theorem axisSlot_hasNoncritical_of_retained_pos
    {A : Type} [Group A] {N : Subgroup A}
    (S : AxisSlot A N)
    (hretained : 0 < slotRetainedHalfSupport S.slot) :
    S.HasNoncritical := by
  by_contra hnone
  unfold AxisSlot.HasNoncritical at hnone
  push Not at hnone
  have hzero : slotRetainedHalfSupport S.slot = 0 := by
    unfold slotRetainedHalfSupport
    apply Finset.sum_eq_zero
    intro c hc
    cases hcolor : S.slot.color c with
    | inl i => simp [retainedCellHalfSupport]
    | inr t => exact False.elim (hnone c t hcolor)
  omega

/-- A certified slot with positive old support has a noncritical cell, by its
uniform old-to-retained comparison. -/
theorem certifiedSlot_hasNoncritical_of_old_pos
    {A : Type} [Group A] {N : Subgroup A} {parameter old : ℕ}
    (S : CertifiedSlot N parameter old) (hold : 0 < old) :
    S.axisSlot.HasNoncritical := by
  apply axisSlot_hasNoncritical_of_retained_pos S.axisSlot
  have hbound := S.old_le_four_retained
  omega

/-- Positive total old support yields a positive occurrence in a canonical
certified word. -/
theorem canonicalCertifiedWord_hasPositiveOccurrence_of_Cold_pos
    {iota X : Type} [Fintype iota] [DecidableEq iota] [Finite X]
    {Omega : iota → Type} [∀ i, Fintype (Omega i)]
    {U : ∀ i, Subgroup (Equiv.Perm (Omega i))}
    {H : Subgroup (Equiv.Perm X)}
    {C : OrbitProfileFromOrbits.Data H U}
    {N Cold : ℕ}
    (W : CanonicalCertifiedWord Omega U H C N Cold)
    (hCold : 0 < Cold) : W.HasPositiveOccurrence := by
  have hsum : 0 < ∑ q, W.oldSupport q := by
    simpa [W.oldSupport_sum] using hCold
  obtain ⟨q,hq,hqpos⟩ := (Finset.sum_pos_iff.mp hsum)
  exact ⟨q,certifiedSlot_hasNoncritical_of_old_pos (W.certified q) hqpos⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedPositivity

end
