import SymmetricSubgroupAsymptotics.BinaryCarrierCanonicalOrbitAxisBridge
import SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeAxis
import SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedRetention

/-!
# Transporting certified physical slots to the canonical orbit axis

A physical witness slot is allowed to use its own representative of the local
orbit action.  The canonical word, on the other hand, uses the chart stored in
`OrbitProfileFromOrbits.Data`.  This file separates the two harmless transports:

* pull a certified slot back along an action isomorphism whose image is the
  witness axis;
* replace the selected-chart fusion axis by `CanonicalOrbitWord.axis` using
  `canonicalAxis_eq_fusionDeletedAxis`.

Neither transport changes the underlying `PhysicalSlot`, hence neither changes
`slotHalfDegree`, `slotRetainedHalfSupport`, `parameter`, or `old`.
-/

open scoped Pointwise

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace BinaryCarrierCertifiedRetention

open BinaryCarrierS16RouteLocalCertificates
open BinaryDegreeEightPhysicalAnalyticClosure

/-- Pull a certified physical slot back along an action isomorphism.

The slot data are literally unchanged by `AxisSlot.pullback`; only the ambient
action and the proof that the slot axis lies in it are transported.  Thus all
three numerical fields of `CertifiedSlot` are reused without arithmetic. -/
def CertifiedSlot.pullback
    {A B : Type} [Group A] [Group B]
    {N : Subgroup A} {parameter old : ℕ}
    (e : A ≃* B)
    (S : CertifiedSlot (N.map e.toMonoidHom) parameter old) :
    CertifiedSlot N parameter old where
  axisSlot := S.axisSlot.pullback e N
  parameter_eq := S.parameter_eq
  retained_le_old := S.retained_le_old
  old_le_four_retained := S.old_le_four_retained

@[simp] theorem CertifiedSlot.pullback_axisSlot_slot
    {A B : Type} [Group A] [Group B]
    {N : Subgroup A} {parameter old : ℕ}
    (e : A ≃* B)
    (S : CertifiedSlot (N.map e.toMonoidHom) parameter old) :
    (S.pullback e).axisSlot.slot = S.axisSlot.slot := rfl

/-- Pull a certified slot back when its witness axis is propositionally, rather
than definitionally, the image of the source axis. -/
def CertifiedSlot.pullbackOfMapEq
    {A B : Type} [Group A] [Group B]
    {N : Subgroup A} {M : Subgroup B} {parameter old : ℕ}
    (e : A ≃* B)
    (haxis : N.map e.toMonoidHom = M)
    (S : CertifiedSlot M parameter old) :
    CertifiedSlot N parameter old where
  axisSlot := {
    slot := S.axisSlot.slot
    sourceEquiv := e.trans S.axisSlot.sourceEquiv
    kernel := by
      change N.map (S.axisSlot.sourceEquiv.toMonoidHom.comp e.toMonoidHom) =
        S.axisSlot.slot.alpha.ker
      rw [← Subgroup.map_map,haxis]
      exact S.axisSlot.kernel }
  parameter_eq := S.parameter_eq
  retained_le_old := S.retained_le_old
  old_le_four_retained := S.old_le_four_retained

@[simp] theorem CertifiedSlot.pullbackOfMapEq_axisSlot_slot
    {A B : Type} [Group A] [Group B]
    {N : Subgroup A} {M : Subgroup B} {parameter old : ℕ}
    (e : A ≃* B) (haxis : N.map e.toMonoidHom = M)
    (S : CertifiedSlot M parameter old) :
    (S.pullbackOfMapEq e haxis).axisSlot.slot = S.axisSlot.slot := rfl

/-- Certificate-level form of `CertifiedSlot.pullback`.

This is useful when the stored finite witness exposes an `AxisSlot` and an
exact `Certificate` rather than an already packaged `CertifiedSlot`. -/
def CertifiedSlot.ofCertificatePullback
    {A B : Type} [Group A] [Group B]
    {N : Subgroup A} {parameter retained old : ℕ}
    (e : A ≃* B)
    (S : AxisSlot B (N.map e.toMonoidHom))
    (cert : Certificate S.slot parameter retained)
    (hle : retained ≤ old)
    (hquarter : old ≤ 4 * retained) :
    CertifiedSlot N parameter old :=
  CertifiedSlot.ofCertificate
    (S.pullback e N)
    (Certificate.pullback e S cert)
    hle hquarter

end BinaryCarrierCertifiedRetention

namespace BinaryCarrierCanonicalCertifiedSlotBridge

open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierCertifiedRetention
open BinaryDegreeEightPhysicalAnalyticClosure
open FusionOrbitRepresentativeAxis

section Representative

variable {n w : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin n)))
variable (x : Fin n)
variable (hw : Nat.card (MulAction.orbit H x) = w)

/-- A certified slot stored on the actual witness representative pulls back to
any local chart realizing the same orbit image.  No equality between the local
chart and the witness chart is required: `localActionEquiv` is the needed
fusion-natural action equivalence, and
`localDeletedAxis_map_symm_eq` supplies its exact axis image. -/
def certifiedSlotOfLocalDeletedAxis
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet H x)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H))
    {parameter old : ℕ}
    (S : CertifiedSlot
      (actualDeletedModel H x hw).goursatFst parameter old) :
    CertifiedSlot
      (localDeletedModel H x hw e U).goursatFst parameter old :=
  S.pullbackOfMapEq
    (localActionEquiv H x hw e U himage).symm
    (localDeletedAxis_map_symm_eq H x hw e U himage)

end Representative

section Canonical

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Z : Type} [Fintype Z] [DecidableEq Z]
variable (Ω : ι → Type)
variable [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
variable (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
variable (H : Subgroup (Equiv.Perm X))
variable (C : OrbitProfileFromOrbits.Data H U)

/-- Transport a certified physical witness from any action representative to
`CanonicalOrbitWord.axis`.

The caller need only prove the fusion-natural axis-image statement for the
selected canonical chart.  In the representative-chart application this is
exactly `FusionOrbitRepresentativeAxis.localDeletedAxis_map_symm_eq`; the
separate equality supplied by `canonicalAxis_eq_fusionDeletedAxis` then makes
that statement apply to the canonical word axis.  No chart equality is part of
the interface. -/
def certifiedSlotOfCanonicalFusionAxis
    (q : Σ i, Fin (C.multiplicity i))
    (eC : Z ≃ ↥((FusionOrbitProfileChart.orbitSubaction
      H (C.orbitIndex q))ᶜ))
    {B : Type} [Group B]
    (e : U q.1 ≃* B)
    (M : Subgroup B)
    (haxis :
      ((fusionDeletedModel (U q.1)
        (relabelSubgroup
          (BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
            Ω U H C q eC).symm H)).goursatFst).map e.toMonoidHom = M)
    {parameter old : ℕ}
    (S : CertifiedSlot M parameter old) :
    CertifiedSlot (CanonicalOrbitWord.axis Ω U H C q) parameter old := by
  apply S.pullbackOfMapEq e
  calc
    (CanonicalOrbitWord.axis Ω U H C q).map e.toMonoidHom =
        ((fusionDeletedModel (U q.1)
          (relabelSubgroup
            (BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
              Ω U H C q eC).symm H)).goursatFst).map e.toMonoidHom := by
      rw [BinaryCarrierCanonicalOrbitAxisBridge.canonicalAxis_eq_fusionDeletedAxis
        Ω U H C q eC]
    _ = M := haxis

@[simp] theorem certifiedSlotOfCanonicalFusionAxis_axisSlot_slot
    (q : Σ i, Fin (C.multiplicity i))
    (eC : Z ≃ ↥((FusionOrbitProfileChart.orbitSubaction
      H (C.orbitIndex q))ᶜ))
    {B : Type} [Group B]
    (e : U q.1 ≃* B)
    (M : Subgroup B)
    (haxis :
      ((fusionDeletedModel (U q.1)
        (relabelSubgroup
          (BinaryCarrierCanonicalOrbitAxisBridge.selectedChart
            Ω U H C q eC).symm H)).goursatFst).map e.toMonoidHom = M)
    {parameter old : ℕ}
    (S : CertifiedSlot M parameter old) :
    (certifiedSlotOfCanonicalFusionAxis Ω U H C q eC e M haxis S).axisSlot.slot =
      S.axisSlot.slot := by
  unfold certifiedSlotOfCanonicalFusionAxis
  simp

end Canonical

end BinaryCarrierCanonicalCertifiedSlotBridge

end SymmetricSubgroupAsymptotics

end
