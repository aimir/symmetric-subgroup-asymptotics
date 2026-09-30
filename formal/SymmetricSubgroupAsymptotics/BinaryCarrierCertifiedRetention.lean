import SymmetricSubgroupAsymptotics.BinaryCarrierS16RouteLocalCertificates

/-!
# Certified local slots and exact whole-word retention

The finite route certificates are local.  This file packages exactly the
data needed to add them over a simultaneous carrier word: physical
half-degree, old retained support, and the two pointwise retention
inequalities.  The global `Retention` record is then canonical by the
literal-cell Fubini identity.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedRetention

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierRetentionNumerics
open BinaryCarrierRoutedWordClosure
open BinaryCarrierS16RouteLocalCertificates
open BinaryCarrierWordClosure
open BinaryDegreeEightPhysicalAnalyticClosure

/-- One exact-axis slot with all numerical data needed for word assembly.
`parameter` is its physical half-degree; `old` is the support charged to the
original residual state. -/
structure CertifiedSlot {A : Type} [Group A] (N : Subgroup A)
    (parameter old : ℕ) where
  axisSlot : AxisSlot A N
  parameter_eq : slotHalfDegree axisSlot.slot = parameter
  retained_le_old : slotRetainedHalfSupport axisSlot.slot ≤ old
  old_le_four_retained : old ≤ 4 * slotRetainedHalfSupport axisSlot.slot

/-- Change only the two numerical indices of a certified slot.  The physical
slot is retained definitionally, which is useful when a certificate-dependent
arithmetic equality should not obscure its point chart. -/
def CertifiedSlot.reindex
    {A : Type} [Group A] {N : Subgroup A}
    {parameter old parameter' old' : ℕ}
    (S : CertifiedSlot N parameter old)
    (hparameter : parameter = parameter') (hold : old = old') :
    CertifiedSlot N parameter' old' where
  axisSlot := S.axisSlot
  parameter_eq := S.parameter_eq.trans hparameter
  retained_le_old := S.retained_le_old.trans_eq hold
  old_le_four_retained := hold.symm.le.trans S.old_le_four_retained

@[simp] theorem CertifiedSlot.reindex_axisSlot_slot
    {A : Type} [Group A] {N : Subgroup A}
    {parameter old parameter' old' : ℕ}
    (S : CertifiedSlot N parameter old)
    (hparameter : parameter = parameter') (hold : old = old') :
    (S.reindex hparameter hold).axisSlot.slot = S.axisSlot.slot := rfl

/-- Build a general certified slot from an exact route-local calculation. -/
def CertifiedSlot.ofCertificate
    {A : Type} [Group A] {N : Subgroup A}
    {parameter retained old : ℕ}
    (S : AxisSlot A N) (h : Certificate S.slot parameter retained)
    (hle : retained ≤ old) (hquarter : old ≤ 4 * retained) :
    CertifiedSlot N parameter old where
  axisSlot := S
  parameter_eq := h.halfDegree
  retained_le_old := h.retainedHalfSupport.le.trans hle
  old_le_four_retained := hquarter.trans_eq
    (congrArg (fun x => 4 * x) h.retainedHalfSupport.symm)

/-- A positive route occupies one original orbit, so its physical half-degree
and old support coincide. -/
structure CertifiedPositiveAxisSlot {A : Type} [Group A]
    (N : Subgroup A) (old : ℕ) : Type 2 extends CertifiedSlot N old old where
  hasNoncritical : axisSlot.HasNoncritical

/-- Turn an exact route-local calculation into the numerical word interface. -/
def CertifiedPositiveAxisSlot.ofCertificate
    {A : Type} [Group A] {N : Subgroup A} {old retained : ℕ}
    (S : AxisSlot A N) (hs : S.HasNoncritical)
    (h : Certificate S.slot old retained)
    (hle : retained ≤ old) (hquarter : old ≤ 4 * retained) :
    CertifiedPositiveAxisSlot N old :=
  { CertifiedSlot.ofCertificate S h hle hquarter with
    hasNoncritical := hs }

section Word

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : ι → Type} [∀ i, Group (A i)]
  (N : ∀ i, Subgroup (A i))
  (parameter old : ι → ℕ)
  (C : ∀ i, CertifiedSlot (N i) (parameter i) (old i))

/-- Forget the certificates and retain the literal routed slots. -/
def slots (i : ι) : Slot := (C i).axisSlot.slot

/-- The word parameter is exactly the sum of the certified local physical
half-degrees. -/
theorem wordParameter_eq_sum_parameter :
    wordParameter (slots N parameter old C) = ∑ i, parameter i := by
  rw [wordParameter_eq_sum_halfDegree]
  apply Finset.sum_congr rfl
  intro i hi
  exact (C i).parameter_eq

/-- The pointwise certificates assemble without loss into the producer's
global retention record. -/
def retention {Cold : ℕ} (hold : ∑ i, old i = Cold) :
    Retention (slots N parameter old C) Cold :=
  Retention.ofSlotSupport (slots N parameter old C) old hold
    (fun i => (C i).retained_le_old)
    (fun i => (C i).old_le_four_retained)

/-- A positive certified coordinate supplies the whole word's required
noncritical cell. -/
theorem hasNoncritical_of_exists
    (hpositive : ∃ i, (C i).axisSlot.HasNoncritical) :
    ∃ c : Σ i, cells (slots N parameter old C) i, ∃ t,
      colors (slots N parameter old C) c = .inr t := by
  obtain ⟨i,j,t,hj⟩ := hpositive
  exact ⟨⟨i,j⟩,t,hj⟩

end Word

end SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedRetention

end
