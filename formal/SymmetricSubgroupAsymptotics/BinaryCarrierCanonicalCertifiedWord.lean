import SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedRetention
import SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitPhysicalEncoding

/-!
# Certified words on canonical literal-orbit axes

An all-orbit construction supplies one numerical `CertifiedSlot` on every
axis extracted from the simultaneous canonical orbit chart.  This file
packages those local certificates together with their two exact global sums.
The generic Fubini and retention theorems then produce the precise
`SlotWord` data consumed by the dependent physical producer.

No orbit classification, chart comparison, or route choice occurs here.
Those operations belong upstream, where the certified slots are constructed.
In particular this structure is intended to be a deterministic function of
the original subgroup, rather than an extra component of a counted family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalCertifiedWord

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierCertifiedRetention
open BinaryCarrierDependentVariableWordProducer
open BinaryCarrierRetentionNumerics
open BinaryCarrierWordClosure
open BinaryDegreeEightPhysicalAnalyticClosure

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [Finite X]
  (Ω : ι → Type) [∀ i, Fintype (Ω i)]
  (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
  (H : Subgroup (Equiv.Perm X))
  (C : OrbitProfileFromOrbits.Data H U)

/-- One certified exact-axis slot on every literal orbit occurrence, together
with the exact physical-parameter and old-support totals. -/
structure CanonicalCertifiedWord (N Cold : ℕ) where
  parameter : (Σ i, Fin (C.multiplicity i)) → ℕ
  oldSupport : (Σ i, Fin (C.multiplicity i)) → ℕ
  certified : ∀ q : (Σ i, Fin (C.multiplicity i)),
    CertifiedSlot (CanonicalOrbitWord.axis Ω U H C q)
      (parameter q) (oldSupport q)
  parameter_sum : ∑ q, parameter q = N
  oldSupport_sum : ∑ q, oldSupport q = Cold

namespace CanonicalCertifiedWord

variable {Ω U H C} {N Cold : ℕ}
  (W : CanonicalCertifiedWord Ω U H C N Cold)

/-- Forget the numerical certificate at one occurrence and retain its exact
canonical-axis route. -/
def axisSlot (q : Σ i, Fin (C.multiplicity i)) :
    AxisSlot (U q.1) (CanonicalOrbitWord.axis Ω U H C q) :=
  (W.certified q).axisSlot

/-- The heterogeneous word on the complete canonical orbit chart. -/
def slotWord : SlotWord :=
  CanonicalOrbitWord.slotWord Ω U H C W.axisSlot

/-- The parameter of the bundled slot word is the prescribed common
half-degree. -/
theorem slotWord_parameter : W.slotWord.parameter = N := by
  letI : Fintype (Σ i, Fin (C.multiplicity i)) := inferInstance
  letI : DecidableEq (Σ i, Fin (C.multiplicity i)) := Classical.decEq _
  change wordParameter (fun q => (W.certified q).axisSlot.slot) = N
  calc
    wordParameter (fun q => (W.certified q).axisSlot.slot) =
        ∑ q, slotHalfDegree (W.certified q).axisSlot.slot :=
      wordParameter_eq_sum_halfDegree _
    _ = ∑ q, W.parameter q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (W.certified q).parameter_eq
    _ = N := W.parameter_sum

/-- The unbundled producer retention record assembled from the local
certificates. -/
def retention :
    Retention (fun q => (W.certified q).axisSlot.slot) Cold := by
  letI : Fintype (Σ i, Fin (C.multiplicity i)) := inferInstance
  letI : DecidableEq (Σ i, Fin (C.multiplicity i)) := Classical.decEq _
  exact Retention.ofSlotSupport
    (fun q => (W.certified q).axisSlot.slot)
    W.oldSupport W.oldSupport_sum
    (fun q => (W.certified q).retained_le_old)
    (fun q => (W.certified q).old_le_four_retained)

/-- The same retention certificate in the dependent `SlotWord` interface. -/
def retentionAt : W.slotWord.RetentionAt Cold := by
  letI : Fintype (Σ i, Fin (C.multiplicity i)) := inferInstance
  letI : DecidableEq (Σ i, Fin (C.multiplicity i)) := Classical.decEq _
  exact W.retention

/-- A certified occurrence is positive when its chosen exact-axis route
displays a noncritical original-action cell. -/
def HasPositiveOccurrence : Prop :=
  ∃ q : (Σ i, Fin (C.multiplicity i)),
    (W.certified q).axisSlot.HasNoncritical

/-- One positive occurrence supplies the noncritical cell required by the
whole bundled word. -/
theorem slotWord_hasNoncritical
    (hpositive : W.HasPositiveOccurrence) : W.slotWord.HasNoncritical := by
  letI : Fintype (Σ i, Fin (C.multiplicity i)) := inferInstance
  letI : DecidableEq (Σ i, Fin (C.multiplicity i)) := Classical.decEq _
  obtain ⟨q,j,t,hj⟩ := hpositive
  exact ⟨⟨q,j⟩,t,hj⟩

/-- A positive canonical certified word is ready for the common retained-bin
target, with its complete correlated canonical source preserved. -/
def routedWord (hpositive : W.HasPositiveOccurrence) : RoutedWord N Cold :=
  CanonicalOrbitWord.routedWord Ω U H C W.axisSlot
    W.slotWord_parameter (W.slotWord_hasNoncritical hpositive) W.retentionAt

end CanonicalCertifiedWord

end SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalCertifiedWord

end
