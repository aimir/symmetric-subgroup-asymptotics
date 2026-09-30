import SymmetricSubgroupAsymptotics.BinaryDegreeEightNormalizerSaturatedDirect
import SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer
import SymmetricSubgroupAsymptotics.BinaryCarrierRoutedWordClosure
import SymmetricSubgroupAsymptotics.CriticalOrbitCriterion

/-!
# Degree-eight carrier residuals and fixed-cell source codes

This file supplies two structural bridges needed by the actual carrier
producer.

First, the zero-support outcome of the degree-eight finite classification is
kept at the `CarrierOwner` level.  At that level it is not merely an arbitrary
slot whose displayed colours happen to be E8: the original literal orbit
action is actually the critical E8 action.  Thus a pure E8 word can be returned
to the already counted critical owner.

Second, a canonical fixed-axis cell whose actual subgroups are jointly coded
by a bounded decoration and their literal full product model gives a
`SourceCode` after the checked simultaneous routed transport.  The routed word
is fixed on the cell, and injectivity of the coordinate change means that no
orbit or route witness is added to the counted source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightCarrierSourceBridge

open SymmetricSubgroupAsymptotics
open BinaryDegreeEightBaseRoutes
open BinaryActionRegistry8
open BinaryDegreeEightPhysicalAnalyticClosure
open BinaryDegreeEightNormalizerSaturatedDirect
open BinaryCarrierWordClosure
open BinaryCarrierRoutedWordClosure
open BinaryCarrierActualDecoratedProducer

/-! ## The genuine zero-support outcome -/

/-- The literal eight-point action is the original critical E8 permutation
action, up to a point relabelling. -/
def IsE8Action (U : Subgroup (Equiv.Perm (Fin 8))) : Prop :=
  ∃ e : criticalActionPoints .e8 ≃ Fin 8,
    relabelSubgroup e (criticalActionSubgroup .e8) = U

/-- Among the unchanged degree-eight base colours, every colour except E8 has
positive completed-mixture support. -/
theorem base_noncritical_or_e8 (b : Base) :
    (∃ t, baseKind b = .inr t) ∨ b = .e8 := by
  cases b with
  | t18 => exact Or.inl ⟨some (.degree8 .t18),rfl⟩
  | e8 => exact Or.inr rfl
  | t26 => exact Or.inl ⟨some (.degree8 .t26),rfl⟩
  | t27 => exact Or.inl ⟨some (.degree8 .t27),rfl⟩
  | t28 => exact Or.inl ⟨some (.degree8 .t28),rfl⟩
  | t29 => exact Or.inl ⟨some (.degree8 .t29),rfl⟩
  | t31 => exact Or.inl ⟨some (.degree8 .t31),rfl⟩
  | t35 => exact Or.inl ⟨some (.degree8 .t35),rfl⟩

/-- A degree-eight carrier owner either supplies a genuinely positive-support
slot or proves that the original action itself is E8.  Keeping the conclusion
at owner level is essential: `AxisSlot.IsPureE8` by itself does not constrain
an arbitrary user-supplied slot strongly enough to identify its source action.
-/
theorem supportedAxisSlot_or_isE8Action
    {U : Subgroup (Equiv.Perm (Fin 8))}
    {N : Subgroup U} [N.Normal] (O : CarrierOwner U N) :
    Nonempty {S : AxisSlot U N // S.HasNoncritical} ∨ IsE8Action U := by
  rcases O with ⟨b,g,hg⟩ | ⟨i,g,hg,e,hsource,haxis⟩
  · rcases base_noncritical_or_e8 b with ⟨t,ht⟩ | rfl
    · left
      let S := baseAxisSlot b g hg N
      refine ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,?_⟩⟩
      change ∃ c : Fin 1, ∃ t, baseKind b = .inr t
      exact ⟨0,t,ht⟩
    · right
      refine ⟨(basePointEquiv .e8).trans g.symm,?_⟩
      change relabelSubgroup g U = actions (baseIndex .e8) at hg
      calc
        relabelSubgroup ((basePointEquiv .e8).trans g.symm)
            (criticalActionSubgroup .e8) =
            relabelSubgroup g.symm
              (relabelSubgroup (basePointEquiv .e8)
                (criticalActionSubgroup .e8)) :=
          (relabelSubgroup_trans (basePointEquiv .e8) g.symm _).symm
        _ = relabelSubgroup g.symm (actions (baseIndex .e8)) := by
          exact congrArg (relabelSubgroup g.symm) (base_action_eq .e8)
        _ = relabelSubgroup g.symm (relabelSubgroup g U) := by rw [hg]
        _ = U := relabelSubgroup_symm g U
  · left
    fin_cases e
    · let S := t16AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      exact ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,
        t16AxisSlot_hasNoncritical i hsource _ haxis⟩⟩
    · let S := t20AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      exact ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,
        t20AxisSlot_hasNoncritical i hsource _ haxis⟩⟩
    · let S := t21AxisSlot i hsource (actionConjugacyNormal g hg N) haxis
      exact ⟨⟨S.pullback (actionConjugacyEquiv g hg) N,
        t21AxisSlot_hasNoncritical i hsource _ haxis⟩⟩

/-- The intrinsic earlier-owner statement on the actual original orbit. -/
def IsE8Orbit {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))} (W : OrbitWitness H) : Prop :=
  ∃ e : criticalActionPoints .e8 ≃ MulAction.orbit H W.point,
    relabelSubgroup e (criticalActionSubgroup .e8) =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H)

/-- The local E8 action conclusion is exactly the original-orbit E8
conclusion after composing with the canonical actual orbit chart. -/
theorem isE8Orbit_of_isE8Action {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))} (W : OrbitWitness H)
    (hE8 : IsE8Action W.action) : IsE8Orbit W := by
  obtain ⟨e,he⟩ := hE8
  let c := FusionActualOrbitCharts.orbitEquiv H W.point W.orbit_card
  refine ⟨e.trans c,?_⟩
  calc
    relabelSubgroup (e.trans c) (criticalActionSubgroup .e8) =
        relabelSubgroup c
          (relabelSubgroup e (criticalActionSubgroup .e8)) :=
      (relabelSubgroup_trans e c _).symm
    _ = relabelSubgroup c W.action := by rw [he]
    _ = OrbitProfileFromOrbits.orbitImage H
          (Quotient.mk'' W.point : OrbitProfileFromOrbits.Orbit H) := by
      change relabelSubgroup c
          (FusionActualOrbitCharts.chartAction H W.point W.orbit_card) = _
      rw [FusionActualOrbitCharts.chartAction_eq_map]
      exact relabelSubgroup_symm c.symm _

/-- Every actual degree-eight witness in the unmarked carrier residual either
provides positive support or is already an E8 critical orbit. -/
theorem carrierResidual_supportedSlot_or_isE8Orbit {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ carrierResidualFamily n) (W : OrbitWitness H) :
    Nonempty {S : AxisSlot W.action W.axis // S.HasNoncritical} ∨
      IsE8Orbit W := by
  rcases supportedAxisSlot_or_isE8Action
      (carrierResidual_all_witnesses hH W) with
    hsupported | hE8
  · exact Or.inl hsupported
  · exact Or.inr (isE8Orbit_of_isE8Action W hE8)

/-! ## Canonical fixed cells feed the actual decorated producer -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]
  (N : ∀ i, Subgroup (A i))
  (R : ∀ i, AxisSlot (A i) (N i))

/-- Source-side data on one canonical residual cell.  The cell fixes the whole
heterogeneous routed word.  Its model is the literal full product subgroup with
its canonical exact axes; only the bounded reconstruction decoration may vary.
-/
structure FixedAxisCellCode (Actual : Type*) (Cold K : ℕ) where
  Decoration : Type
  decorationFinite : Finite Decoration
  decoration : Actual → Decoration
  model : Actual → ExactAxisFamily A N
  joint_injective :
    Function.Injective (fun H ↦ (decoration H, model H))
  decoration_card_le :
    Nat.card Decoration ≤
      (2 * wordParameter (slots A N R) + 2) ^ (K * (2 * Cold))

namespace FixedAxisCellCode

/-- The checked coordinatewise route turns a canonical fixed-axis cell code
into the exact `SourceCode` required by the actual decorated producer. -/
def toSourceCode {Actual : Type*} {Cold K : ℕ}
    (E : FixedAxisCellCode A N R Actual Cold K) :
    SourceCode (slots A N R) Actual Cold K where
  Decoration := E.Decoration
  decorationFinite := E.decorationFinite
  decoration := E.decoration
  word := fun H ↦ routedSource A N R (E.model H)
  joint_injective := by
    intro H H' h
    have hdecoration : E.decoration H = E.decoration H' :=
      congrArg (fun z : E.Decoration × WordSource (slots A N R) ↦ z.1) h
    have hword :
        routedSource A N R (E.model H) = routedSource A N R (E.model H') :=
      congrArg (fun z : E.Decoration × WordSource (slots A N R) ↦ z.2) h
    apply E.joint_injective
    apply Prod.ext
    · exact hdecoration
    · apply routedSource_injective A N R
      exact hword
  decoration_card_le := E.decoration_card_le

end FixedAxisCellCode

end SymmetricSubgroupAsymptotics.BinaryDegreeEightCarrierSourceBridge

end
