import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelTargetAccessors
import SymmetricSubgroupAsymptotics.BinaryS16TargetCastAccessor

/-!
# Exact target orbits for the direct S16 word

The public direct target is cast in its half-degree and old-support indices.
This file removes those two numerical casts at the semantic boundary and
recovers fullness on the exact fusion-natural chart over the original labels.
The chart itself remains uncounted.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16TargetOrbitAccessor

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierOriginalLabelTargetAccessors
open BinaryCarrierOriginalLabelWordTarget
open BinaryCarrierProfileTransport
open BinaryS16DirectPhysicalTarget
open BinaryS16TargetCastAccessor

variable {N : ℕ} (C : BinaryS16DirectFixedSupportClosure.SupportIndex N)

/-- Before the outer numeric cast, the target is full on the precise supplied
word chart used by the producer. -/
theorem rawTarget_full (H : Actual C) :
    OrbitProfileFullOn mixtureAction (wordPointChart C H)
      (rawTarget C H).2.1 := by
  have hfull := wordPhysicalTargetOn_full
    (slot C H) (wordPointChart C H) (wordSource C H)
  simpa [rawTarget,wordTargetOn] using hfull

/-- The public target subgroup is full on the exact fusion-natural point
chart on the original `Fin (2*N)` labels. -/
theorem targetSubgroup_full (H : Actual C) :
    OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart
        (subgroup C H) (residualSector C H))
      (relabelSubgroup
        (Equiv.cast (congrArg (fun M : ℕ ↦ Fin (2 * M))
          (parameter_eq C H)))
        (rawTarget C H).2.1) := by
  let e := Equiv.cast (congrArg (fun M : ℕ ↦ Fin (2 * M))
    (parameter_eq C H))
  have hfull := (rawTarget_full C H).relabel e
  have hchart : (wordPointChart C H).trans e =
      BinaryS16FusionNaturalPointChart.pointChart
        (subgroup C H) (residualSector C H) := by
    dsimp [e]
    unfold wordPointChart
    rw [Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]
  rw [hchart] at hfull
  exact hfull

end SymmetricSubgroupAsymptotics.BinaryS16TargetOrbitAccessor

end
