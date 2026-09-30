import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelTargetAccessors

/-!
# The faithful ambient embedding behind a supplied-chart word target

The supplied-chart physical target is a sequence of four faithful maps: the
literal carrier inclusion, the fixed colour display, the independent orbit
action, and conjugation by the supplied point chart.  This file names their
composite.  Exposing it lets a varying-word decoder compare two physical
targets in the common original labelled permutation group before their
dependent quotient types have been identified.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelEmbedding

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierCellProfile
open BinaryCarrierOriginalLabelPhysicalTarget
open BinaryCarrierOriginalLabelTargetAccessors
open BinaryCarrierOriginalLabelWordTarget
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  (slot : ι → Slot)

private abbrev targetMultiplicity :=
  profileMultiplicity
    (criticalRank (cells slot) (colors slot))
    (cyclicMultiplicity (cells slot) (colors slot))
    (carrierScale (cells slot) (colors slot))
    (index (cells slot) (colors slot))

/-- The faithful action of the complete replacement-carrier product on the
supplied original labels. -/
def ambientEmbedding
    (e : OrbitProfilePoints mixturePoints (targetMultiplicity slot) ≃ X) :
    (∀ i, carriers slot i) →* Equiv.Perm X :=
  e.permCongrHom.toMonoidHom.comp
    ((orbitProfileProductAction (targetMultiplicity slot) mixtureAction).comp
      (((originalColorDisplay (cells slot) (colors slot)).productEquiv.toMonoidHom).comp
        (carrierReplacementEmbedding (carriers slot))))

/-- Every stage of `ambientEmbedding` is faithful. -/
theorem ambientEmbedding_injective
    (e : OrbitProfilePoints mixturePoints (targetMultiplicity slot) ≃ X) :
    Function.Injective (ambientEmbedding slot e) := by
  have h := e.permCongrHom.injective.comp
    ((orbitProfileProductAction_injective
      (targetMultiplicity slot) mixtureAction).comp
      ((originalColorDisplay (cells slot) (colors slot)).productEquiv.injective.comp
        (carrierReplacementEmbedding_injective (carriers slot))))
  simpa only [ambientEmbedding,MonoidHom.coe_comp,Function.comp_apply] using h

/-- The underlying permutation subgroup of a supplied-chart word target is
exactly carrier transport mapped through the faithful ambient embedding. -/
theorem wordPhysicalTargetOn_subgroup
    (e : WordPointChart slot) (H : WordSource slot) :
    (wordPhysicalTargetOn slot e H).1 =
      (carrierTransport (alphas slot) (betas slot) H.1).map
        (ambientEmbedding slot e) := by
  let J := physicalTransportOn
    (C := carriers slot)
    (hC := fun i => (slot i).carrierFull)
    (α := alphas slot)
    (β := betas slot)
    (hα := fun i => (slot i).alphaSurjective)
    (hβ := fun i => (slot i).betaSurjective)
    (s := index (cells slot) (colors slot))
    (Dmix := originalColorDisplay (cells slot) (colors slot)) e H
  rw [show (wordPhysicalTargetOn slot e H).1 = J.1 by
    exact physicalFamily_cast_rank_val
      (BinaryCarrierActualDecoratedProducer.wordParameter_sub_wordSupport
        slot).symm J]
  unfold J physicalTransportOn ProfileDisplay.physicalTargetOn
  unfold ProfileDisplay.modelTarget ProfileDisplay.productTarget
  unfold orbitProfileProductFullEquiv relabelSubgroup
  unfold carrierTransportRecords carrierTransportInAmbient
  change
    ((((carrierTransport (alphas slot) (betas slot) H.1).map
        (carrierReplacementEmbedding (carriers slot))).map
      (originalColorDisplay (cells slot) (colors slot)).productEquiv.toMonoidHom).map
      (orbitProfileProductAction (targetMultiplicity slot) mixtureAction)).map
      e.permCongrHom.toMonoidHom = _
  unfold ambientEmbedding
  simp only [Subgroup.map_map]

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelEmbedding

end
