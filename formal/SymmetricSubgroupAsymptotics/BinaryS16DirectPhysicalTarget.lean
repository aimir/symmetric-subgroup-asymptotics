import SymmetricSubgroupAsymptotics.BinaryS16DirectFixedSupportClosure
import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelWordTarget
import SymmetricSubgroupAsymptotics.BinaryS16CanonicalMixedBlockTable
import SymmetricSubgroupAsymptotics.BinaryS16FusionNaturalPointChart
import SymmetricSubgroupAsymptotics.BinaryS16JointCertifiedWord
import SymmetricSubgroupAsymptotics.BinaryCarrierFusionEmbeddingFormula

/-!
# The direct physical target on one fixed-support fibre

Each subgroup in a direct fixed-support fibre supplies its complete correlated
source together with a fusion-natural chart from the displayed route cells to
the subgroup's original ambient labels.  The supplied-chart word transport is
then cast only in its two numerical indices.  In particular, no canonical
relabelling of unchanged critical or cyclic-four blocks occurs here.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16DirectPhysicalTarget

private theorem trans_symm_trans_self
    {A X Y : Type*} (f : A ≃ X) (p : Y ≃ X) :
    (f.trans p.symm).trans p = f := by
  apply Equiv.ext
  intro x
  exact p.apply_symm_apply _

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalCertifiedWord
open BinaryCarrierCanonicalOrbitPhysicalEncoding
open BinaryCarrierOriginalLabelWordTarget
open BinaryCarrierWordClosure
open BinaryS16CanonicalCarrierProfile
open BinaryS16DirectFixedSupportClosure

variable {N : ℕ} (C : SupportIndex N)

abbrev Actual := FixedSupportFamily N C

def subgroup (H : Actual C) : Subgroup (Equiv.Perm (Fin (2 * N))) :=
  H.1.1.1

def residualSector (H : Actual C) : ResidualSector (subgroup C H) := H.1.1.2

theorem oldSupport_pos (H : Actual C) :
    0 < BinaryS16JointOrbitData.oldSupport (subgroup C H) (residualSector C H) :=
  H.1.2

theorem oldSupport_eq (H : Actual C) :
    BinaryS16JointOrbitData.oldSupport (subgroup C H) (residualSector C H) =
      C.1.1 :=
  congrArg (fun c : SupportIndex N ↦ c.1.1) H.2

/-- The mixed route table, cast only along the fixed-support equality. -/
def blocks (H : Actual C) :
    BinaryDegreeEightSixteenPhysicalDecoration.CanonicalMixedBlockTable
      N C.1.1 :=
  cast
    (congrArg
      (BinaryDegreeEightSixteenPhysicalDecoration.CanonicalMixedBlockTable N)
      (oldSupport_eq C H))
    (BinaryS16CanonicalMixedBlockTable.table
      (subgroup C H) (residualSector C H))

/-- The exact routed slot family of this subgroup. -/
abbrev slot (H : Actual C) :=
  BinaryS16FusionNaturalPointChart.routeSlot
    (subgroup C H) (residualSector C H)

/-- The route word occupies exactly the ambient half-degree. -/
theorem parameter_eq (H : Actual C) :
    BinaryCarrierActualDecoratedProducer.wordParameter (slot C H) = N :=
  (BinaryS16JointCertifiedWord.certifiedWord
    (subgroup C H) (residualSector C H)).slotWord_parameter

/-- The complete correlated canonical source on the exact route slots. -/
def wordSource (H : Actual C) :
    BinaryCarrierActualDecoratedProducer.WordSource (slot C H) := by
  exact CanonicalOrbitWord.sourceAt
    (BinaryS16JointOrbitData.Points (subgroup C H) (residualSector C H))
    (BinaryS16JointOrbitData.action (subgroup C H) (residualSector C H))
    (subgroup C H)
    (BinaryS16JointOrbitData.data (subgroup C H) (residualSector C H))
    (BinaryS16JointCertifiedWord.certifiedWord
      (subgroup C H) (residualSector C H)).axisSlot

/-- Positive direct old support supplies the noncritical route cell required
by the retained-bin producer. -/
theorem hasNoncritical (H : Actual C) :
    ∃ c : Σ i, BinaryCarrierWordClosure.cells (slot C H) i,
      ∃ t, BinaryCarrierWordClosure.colors (slot C H) c = .inr t :=
  (BinaryS16JointCertifiedWord.certifiedWord
    (subgroup C H) (residualSector C H)).slotWord_hasNoncritical
      (BinaryS16JointCertifiedWord.certifiedWord_hasPositiveOccurrence
        (subgroup C H) (residualSector C H) (oldSupport_pos C H))

/-- Exact retention data for the same routed word. -/
def retention (H : Actual C) :
    BinaryCarrierActualDecoratedProducer.Retention (slot C H)
      (BinaryS16JointOrbitData.oldSupport
        (subgroup C H) (residualSector C H)) :=
  (BinaryS16JointCertifiedWord.certifiedWord
    (subgroup C H) (residualSector C H)).retention

/-- The exact point cast from the native word degree to the fixed ambient
degree. -/
abbrev wordParameterCast (H : Actual C) :
    Fin (2 * BinaryCarrierActualDecoratedProducer.wordParameter (slot C H)) ≃
      Fin (2 * N) :=
  Equiv.cast (congrArg (fun M : ℕ => Fin (2 * M)) (parameter_eq C H))

/-- Literal displayed points assembled on the fixed original ambient labels. -/
def fixedLiteralPointChart (H : Actual C) :
    BinaryCarrierFusionEmbeddingFormula.LiteralPoints (slot C H) ≃ Fin (2 * N) :=
  BinaryCarrierFusionEmbeddingFormula.literalPointChart
    (slot C H)
    (fun q => BinaryS16JointOrbitData.Points
      (subgroup C H) (residualSector C H) q.1)
    (BinaryS16FusionNaturalPointChart.slotChart
      (subgroup C H) (residualSector C H))
    (BinaryS16FusionNaturalPointChart.assemble
      (subgroup C H) (residualSector C H))

/-- The literal displayed points on the native word degree. -/
def wordLiteralPointChart (H : Actual C) :
    BinaryCarrierFusionEmbeddingFormula.LiteralPoints (slot C H) ≃
      Fin (2 * BinaryCarrierActualDecoratedProducer.wordParameter (slot C H)) :=
  (fixedLiteralPointChart C H).trans (wordParameterCast C H).symm

/-- Stable outer shape of the native literal chart. -/
theorem wordLiteralPointChart_eq (H : Actual C) :
    wordLiteralPointChart C H =
      (fixedLiteralPointChart C H).trans (wordParameterCast C H).symm := rfl

/-- Returning the native literal chart through the exact parameter cast
recovers the fixed original-label chart. -/
theorem wordLiteralPointChart_trans_parameterCast (H : Actual C) :
    (wordLiteralPointChart C H).trans (wordParameterCast C H) =
      fixedLiteralPointChart C H := by
  calc
    (wordLiteralPointChart C H).trans (wordParameterCast C H) =
      ((fixedLiteralPointChart C H).trans
        (wordParameterCast C H).symm).trans (wordParameterCast C H) :=
      congrArg (fun e => e.trans (wordParameterCast C H))
        (wordLiteralPointChart_eq C H)
    _ = fixedLiteralPointChart C H :=
      trans_symm_trans_self (fixedLiteralPointChart C H)
        (wordParameterCast C H)

/-- Recast the checked fusion-natural chart only along the exact half-degree
identity expected by the generic word-target interface. -/
def wordPointChart (H : Actual C) : WordPointChart (slot C H) :=
  (BinaryS16FusionNaturalPointChart.pointChart
      (subgroup C H) (residualSector C H)).trans
    (wordParameterCast C H).symm

/-- On the native word degree, the abstract completed-profile embedding is
exactly the literal simultaneous carrier action. -/
theorem ambientEmbedding_wordPointChart (H : Actual C) :
    BinaryCarrierOriginalLabelEmbedding.ambientEmbedding
        (slot C H) (wordPointChart C H) =
      (wordLiteralPointChart C H).permCongrHom.toMonoidHom.comp
        (BinaryCarrierFusionEmbeddingFormula.literalAction (slot C H)) := by
  exact BinaryCarrierFusionEmbeddingFormula.ambientEmbedding_pointChart_trans
    (slot C H)
    (fun q => BinaryS16JointOrbitData.Points
      (subgroup C H) (residualSector C H) q.1)
    (BinaryS16FusionNaturalPointChart.slotChart
      (subgroup C H) (residualSector C H))
    (BinaryS16FusionNaturalPointChart.assemble
      (subgroup C H) (residualSector C H))
    (wordParameterCast C H).symm

/-- The original-label target before the two fixed-support numerical casts. -/
def rawTarget (H : Actual C) :
    BinaryCarrierActualDecoratedTransport.Target
      (BinaryCarrierActualDecoratedProducer.wordParameter (slot C H))
      (BinaryS16JointOrbitData.oldSupport
        (subgroup C H) (residualSector C H)) :=
  wordTargetOn (slot C H) (wordPointChart C H)
    (hasNoncritical C H) (retention C H) (wordSource C H)

/-- Reindex a retained target in its two numerical indices.  Naming this
operation keeps later semantic accessors from unfolding the complete S16
word merely to recognize an equality cast. -/
def reindexTarget {M N Cold Cold' : ℕ}
    (hM : M = N) (hCold : Cold = Cold') :
    BinaryCarrierActualDecoratedTransport.Target M Cold →
      BinaryCarrierActualDecoratedTransport.Target N Cold' :=
  cast (congrArg₂ BinaryCarrierActualDecoratedTransport.Target hM hCold)

/-- Reindexing relabels the underlying target subgroup by the corresponding
cast equivalence of ambient point sets. -/
theorem reindexTarget_subgroup {M N Cold Cold' : ℕ}
    (hM : M = N) (hCold : Cold = Cold')
    (t : BinaryCarrierActualDecoratedTransport.Target M Cold) :
    (reindexTarget hM hCold t).2.1 =
      relabelSubgroup
        (Equiv.cast (congrArg (fun L : ℕ ↦ Fin (2 * L)) hM)) t.2.1 := by
  subst N
  subst Cold'
  simp [reindexTarget]

/-- The fusion-natural retained-bin target of a direct fixed-support residual
subgroup, realized on its original `Fin (2*N)` labels. -/
def target (H : Actual C) :
    BinaryCarrierActualDecoratedTransport.Target N C.1.1 :=
  reindexTarget (parameter_eq C H) (oldSupport_eq C H) (rawTarget C H)

end SymmetricSubgroupAsymptotics.BinaryS16DirectPhysicalTarget

end
