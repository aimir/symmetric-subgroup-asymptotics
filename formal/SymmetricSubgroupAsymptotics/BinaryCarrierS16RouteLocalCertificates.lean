import SymmetricSubgroupAsymptotics.BinaryCarrierRetentionNumerics
import SymmetricSubgroupAsymptotics.BinaryS16CanonicalCarrierProfile

/-!
# Route-local numerical certificates for the S16 carrier word

The global carrier parameters are defined by colour-fibre cardinalities.  Those
fibre cardinalities use a noncomputable enumeration, so they are a poor target
for route-by-route computation.  `BinaryCarrierRetentionNumerics` proves once
and for all that the global quantities are sums of literal cell weights.

This file computes only those literal finite sums.  Thus the one-C4 and
one-carrier routes reduce to a one-cell sum, while the proper `16T1086` route
reduces to its canonical occurrence type (one C4 occurrence and three D8
occurrences).  No classical colour-fibre enumeration is evaluated.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS16RouteLocalCertificates

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierMenuSlots
open BinaryCarrierOriginalActions
open BinaryCarrierProfileTransport
open BinaryCarrierRetentionNumerics
open BinaryCarrierWordClosure
open BinaryDegreeEightBaseRoutes
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryDegree16CarrierRouting
open BinaryS16CanonicalCarrierProfile

/-! ## One-slot bridge -/

/-- Regard one routed slot as a one-coordinate carrier word. -/
def oneSlotWord (S : Slot) : Fin 1 → Slot := fun _ ↦ S

/-- The two route-local numbers needed by the retained-bin construction. -/
structure Certificate (S : Slot) (N C : ℕ) : Prop where
  halfDegree : slotHalfDegree S = N
  retainedHalfSupport : slotRetainedHalfSupport S = C

/-- The multiplicity-defined word parameter of a one-slot word is its literal
cell half-degree. -/
theorem wordParameter_oneSlot (S : Slot) :
    wordParameter (oneSlotWord S) = slotHalfDegree S := by
  simpa [oneSlotWord] using
    (wordParameter_eq_sum_halfDegree (oneSlotWord S))

/-- The multiplicity-defined retained support of a one-slot word is its
literal cell retained support. -/
theorem wordSupport_oneSlot (S : Slot) :
    wordSupport (oneSlotWord S) = slotRetainedHalfSupport S := by
  simpa [oneSlotWord] using
    (wordSupport_eq_sum_retainedHalfSupport (oneSlotWord S))

theorem Certificate.wordParameter {S : Slot} {N C : ℕ}
    (h : Certificate S N C) :
    wordParameter (oneSlotWord S) = N :=
  (wordParameter_oneSlot S).trans h.halfDegree

theorem Certificate.wordSupport {S : Slot} {N C : ℕ}
    (h : Certificate S N C) :
    wordSupport (oneSlotWord S) = C :=
  (wordSupport_oneSlot S).trans h.retainedHalfSupport

/-- Pulling an exact-axis slot back to the literal original action changes no
displayed cell and hence preserves its numerical certificate definitionally. -/
theorem Certificate.pullback
    {A B : Type} [Group A] [Group B]
    {M : Subgroup A}
    (e : A ≃* B) (S : AxisSlot B (M.map e.toMonoidHom))
    {P C : ℕ} (h : Certificate S.slot P C) :
    Certificate (S.pullback e M).slot P C :=
  h

/-! ## Canonical quotient-identity cells -/

/-- One unchanged critical cell contributes its physical half-degree and no
retained carrier support. -/
theorem criticalIdentity_certificate
    (i : CriticalActionKind)
    (N : Subgroup (mixtureAction (.inl i))) [N.Normal] :
    Certificate (quotientIdentitySlot (.inl i) N)
      (cellHalfDegree (.inl i)) 0 := by
  cases i <;>
    constructor <;>
    simp [slotHalfDegree, slotRetainedHalfSupport, quotientIdentitySlot,
      identitySlot, cellHalfDegree, retainedCellHalfSupport]

/-- One unchanged regular-C4 cell has half-degree two and retains both
half-points. -/
theorem cyclicFourIdentity_certificate
    (N : Subgroup (mixtureAction (.inr none))) [N.Normal] :
    Certificate (quotientIdentitySlot (.inr none) N) 2 2 := by
  constructor <;>
    simp [slotHalfDegree, slotRetainedHalfSupport, quotientIdentitySlot,
      identitySlot, cellHalfDegree, retainedCellHalfSupport]

/-- One unchanged original carrier cell retains its whole physical half-degree.
This single statement covers every degree-eight base colour and `16T1332`. -/
theorem carrierIdentity_certificate
    (t : BinaryCarrierOriginalActions.Target)
    (N : Subgroup (mixtureAction (.inr (some t)))) [N.Normal] :
    Certificate (quotientIdentitySlot (.inr (some t)) N)
      (4 * factorScaleNat t) (4 * factorScaleNat t) := by
  constructor <;>
    simp [slotHalfDegree, slotRetainedHalfSupport, quotientIdentitySlot,
      identitySlot, cellHalfDegree, retainedCellHalfSupport]

/-! ## Width four -/

/-- The positive width-four branch chosen by the small registry is exactly the
one-cell regular-C4 identity route. -/
theorem cyclicFourAxisSlot_certificate
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (W : SmallOrbitWitness 4 H)
    (e : mixturePoints (.inr none) ≃ Fin 4)
    (he : relabelSubgroup e (mixtureAction (.inr none)) = W.action) :
    Certificate (W.quotientIdentityAxisSlot (.inr none) e he).slot 2 2 := by
  constructor <;>
    simp [SmallOrbitWitness.quotientIdentityAxisSlot, slotHalfDegree,
      slotRetainedHalfSupport, quotientIdentitySlot, identitySlot,
      cellHalfDegree, retainedCellHalfSupport]

/-! ## Degree-eight routes -/

/-- Every non-E8 base route is one unchanged degree-eight original carrier
cell. -/
theorem degreeEightBase_certificate
    {U : Subgroup (Equiv.Perm (Fin 8))}
    (b : Base) (hb : b ≠ .e8) (g : Equiv.Perm (Fin 8))
    (hg : MulAut.conj g • U = BinaryActionRegistry8.actions (baseIndex b))
    (N : Subgroup U) [N.Normal] :
    Certificate (baseAxisSlot b g hg N).slot 4 4 := by
  cases b <;> try contradiction
  all_goals
    constructor <;> simp [baseAxisSlot, baseKind, slotHalfDegree,
      slotRetainedHalfSupport, quotientIdentitySlot, identitySlot,
      cellHalfDegree, retainedCellHalfSupport, factorScaleNat]

/-- The checked `8T16` proper chart displays one degree-eight `8T27` cell. -/
theorem t16_certificate : Certificate t16Slot 4 4 := by
  constructor <;>
    simp [slotHalfDegree, slotRetainedHalfSupport, t16Slot,
      BinaryExceptional8ProfileCarriers.Target, cellHalfDegree,
      retainedCellHalfSupport, factorScaleNat]

/-- The checked `8T20` proper chart displays one degree-eight `8T27` cell. -/
theorem t20_certificate : Certificate t20Slot 4 4 := by
  constructor <;>
    simp [slotHalfDegree, slotRetainedHalfSupport, t20Slot,
      BinaryExceptional8ProfileCarriers.Target, cellHalfDegree,
      retainedCellHalfSupport, factorScaleNat]

/-- The checked `8T21` proper chart displays one degree-eight `8T27` cell. -/
theorem t21_certificate : Certificate t21Slot 4 4 := by
  constructor <;>
    simp [slotHalfDegree, slotRetainedHalfSupport, t21Slot,
      BinaryExceptional8ProfileCarriers.Target, cellHalfDegree,
      retainedCellHalfSupport, factorScaleNat]

/-- Uniform finite exceptional degree-eight statement. -/
theorem degreeEightExceptional_certificate
    (e : Exceptional) (he : e ≠ .t1086) :
    Certificate (exceptionalSlot e) 4 4 := by
  cases e with
  | t16 => exact t16_certificate
  | t20 => exact t20_certificate
  | t21 => exact t21_certificate
  | t1086 => exact False.elim (he rfl)

theorem t16AxisSlot_certificate
    (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T16.Source =
      BinaryActionRegistry8.actions i)
    (M : Subgroup (BinaryActionRegistry8.actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T16.chart.axis =
      M.map (BinaryActionRegistry8.actions i).subtype) :
    Certificate (t16AxisSlot i source M axis).slot 4 4 :=
  t16_certificate

theorem t20AxisSlot_certificate
    (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T20.Source =
      BinaryActionRegistry8.actions i)
    (M : Subgroup (BinaryActionRegistry8.actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T20.chart.axis =
      M.map (BinaryActionRegistry8.actions i).subtype) :
    Certificate (t20AxisSlot i source M axis).slot 4 4 :=
  t20_certificate

theorem t21AxisSlot_certificate
    (i : Fin 26)
    (source : BinaryExceptional8ProfileCarriers.T21.Source =
      BinaryActionRegistry8.actions i)
    (M : Subgroup (BinaryActionRegistry8.actions i)) [M.Normal]
    (axis : BinaryExceptional8ProfileCarriers.T21.chart.axis =
      M.map (BinaryActionRegistry8.actions i).subtype) :
    Certificate (t21AxisSlot i source M axis).slot 4 4 :=
  t21_certificate

/-! ## Degree-sixteen routes -/

/-- The proper `16T1086` carrier has three critical D8 cells and one retained
regular-C4 cell.  The computation is over the explicit canonical occurrence
type, never over a classically enumerated colour fibre. -/
theorem t1086_certificate : Certificate E1086.slot 8 2 := by
  constructor
  · change (∑ j : BinaryExceptional16ProfileCarrier.Occurrence,
        cellHalfDegree j.1) = 8
    native_decide
  · change (∑ j : BinaryExceptional16ProfileCarrier.Occurrence,
        retainedCellHalfSupport j.1) = 2
    native_decide

/-- The routed `16T1086` axis keeps the same four displayed cells. -/
theorem t1086AxisSlot_certificate
    (M : Subgroup BinaryPairBinding16T1086.Original) [M.Normal]
    (O : BinaryExceptional16CyclicOwner.AxisOwner M) :
    Certificate (t1086AxisSlot M O).slot 8 2 :=
  t1086_certificate

/-- The `16T1332` route is one unchanged degree-sixteen original carrier cell. -/
theorem t1332AxisSlot_certificate
    (M : Subgroup BinarySelectedCatalogue16T1332.Original) [M.Normal] :
    Certificate (t1332AxisSlot M).slot 8 8 := by
  let L : Subgroup (mixtureAction t1332Kind) :=
    M.map t1332ActionEquiv.toMonoidHom
  letI : L.Normal :=
    Subgroup.Normal.map inferInstance _ t1332ActionEquiv.surjective
  change Certificate (quotientIdentitySlot t1332Kind L) 8 8
  simpa [t1332Kind, factorScaleNat] using
    (carrierIdentity_certificate (.degree16 .t1332) L)

end SymmetricSubgroupAsymptotics.BinaryCarrierS16RouteLocalCertificates

end
