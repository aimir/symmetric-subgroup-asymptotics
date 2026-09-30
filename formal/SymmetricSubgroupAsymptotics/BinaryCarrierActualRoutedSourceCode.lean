import SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer
import SymmetricSubgroupAsymptotics.BinaryCarrierRoutedWordClosure

/-!
# Routed exact-axis source codes for actual decorated carrier transport

For a fixed product of source groups, fixed literal normal axes, and a fixed
reversible route in every coordinate, the existing routed source map is
already injective.  Consequently that whole layer needs no decoration at all.

This file also isolates the one remaining ambient obligation.  An actual
labelled residual subgroup must be encoded by a canonical fixed-product
exact-axis subgroup, together with only the finite chart data which cannot be
recovered from that subgroup.  Composing this code with `routedSource` gives
the `SourceCode` required by the actual physical producer, without adding a
profile, axis, quotient, or route witness to the counted target.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierActualRoutedSourceCode

open BinaryCarrierActualDecoratedProducer
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierRoutedWordClosure
open BinaryCarrierWordClosure
open BinaryDegreeEightPhysicalAnalyticClosure

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]
  (N : ∀ i, Subgroup (A i))
  (R : ∀ i, AxisSlot (A i) (N i))

/-- The canonical residual cell after the ambient point chart and normal axes
have been fixed.  Its elements are still the actual full subgroups of the
source product; the subsequently fixed `R` selects one slot word for this
cell without becoming data attached to an element. -/
abbrev FixedCell :=
  BinaryCarrierRoutedWordClosure.ExactAxisFamily A N

/-- The slot word carried by the fixed residual cell. -/
abbrev cellSlots (i : ι) : Slot :=
  (R i).slot

/-- A generic `SourceCode` can be counted before it is specialized to a
predicate on permutation subgroups.  This is the abstract finite incidence
bound behind `Transport.source_card_le_bound_mul_sum`. -/
def encodedTarget {Actual : Type*} {Cold K : ℕ}
    (hnoncritical : ∃ c : Σ i, cells (cellSlots A N R) i,
      ∃ t, colors (cellSlots A N R) c = .inr t)
    (Q : Retention (cellSlots A N R) Cold)
    (E : SourceCode (cellSlots A N R) Actual Cold K) :
    Actual → E.Decoration ×
      Target (wordParameter (cellSlots A N R)) Cold :=
  fun H ↦ ⟨E.decoration H,
    wordTarget (cellSlots A N R) hnoncritical Q (E.word H)⟩

theorem encodedTarget_injective {Actual : Type*} {Cold K : ℕ}
    (hnoncritical : ∃ c : Σ i, cells (cellSlots A N R) i,
      ∃ t, colors (cellSlots A N R) c = .inr t)
    (Q : Retention (cellSlots A N R) Cold)
    (E : SourceCode (cellSlots A N R) Actual Cold K) :
    Function.Injective (encodedTarget A N R hnoncritical Q E) := by
  intro H H' h
  have hdecoration : E.decoration H = E.decoration H' :=
    congrArg (fun z : E.Decoration ×
      Target (wordParameter (cellSlots A N R)) Cold ↦ z.1) h
  have htarget :
      wordTarget (cellSlots A N R) hnoncritical Q (E.word H) =
        wordTarget (cellSlots A N R) hnoncritical Q (E.word H') :=
    congrArg (fun z : E.Decoration ×
      Target (wordParameter (cellSlots A N R)) Cold ↦ z.2) h
  apply E.joint_injective
  apply Prod.ext
  · exact hdecoration
  · apply wordTarget_injective (cellSlots A N R) hnoncritical Q
    exact htarget

/-- Arbitrary finite actual source types satisfy the same exact retained-bin
bound as physical residual predicates. -/
theorem sourceCode_card_le_bound_mul_sum
    {Actual : Type*} [Finite Actual] {Cold K : ℕ}
    (hnoncritical : ∃ c : Σ i, cells (cellSlots A N R) i,
      ∃ t, colors (cellSlots A N R) c = .inr t)
    (Q : Retention (cellSlots A N R) Cold)
    (E : SourceCode (cellSlots A N R) Actual Cold K) :
    Nat.card Actual ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin (wordParameter (cellSlots A N R)) Cold,
          Nat.card (PhysicalFamily
            (wordParameter (cellSlots A N R) - binSupport b.1)
            b.1.1.1 b.1.1.2
            (Fin (2 * wordParameter (cellSlots A N R)))) := by
  letI : Finite E.Decoration := E.decorationFinite
  calc
    Nat.card Actual ≤
        Nat.card (E.Decoration ×
          Target (wordParameter (cellSlots A N R)) Cold) :=
      Nat.card_le_card_of_injective
        (encodedTarget A N R hnoncritical Q E)
        (encodedTarget_injective A N R hnoncritical Q E)
    _ = Nat.card E.Decoration *
        Nat.card (Target (wordParameter (cellSlots A N R)) Cold) :=
      Nat.card_prod _ _
    _ ≤ (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold)) *
        Nat.card (Target (wordParameter (cellSlots A N R)) Cold) :=
      Nat.mul_le_mul_right _ E.decoration_card_le
    _ = _ := by rw [Nat.card_sigma]

/-- On one fixed product/axis/route cell, `routedSource` itself is the whole
source code.  The decoration is the singleton type. -/
def fixedCellSourceCode (Cold : ℕ) :
    SourceCode (cellSlots A N R) (FixedCell A N) Cold 0 where
  Decoration := PUnit
  decorationFinite := inferInstance
  decoration := fun _ ↦ PUnit.unit
  word := routedSource A N R
  joint_injective := by
    intro H H' h
    apply routedSource_injective A N R
    exact congrArg Prod.snd h
  decoration_card_le := by simp

/-- Exact retained-bin count for a fixed product, exact axes, and fixed local
routes.  There is no decoration factor at this level. -/
theorem fixedCell_card_le_sum {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells (cellSlots A N R) i,
      ∃ t, colors (cellSlots A N R) c = .inr t)
    (Q : Retention (cellSlots A N R) Cold) :
    Nat.card (FixedCell A N) ≤
      ∑ b : RetainedBin (wordParameter (cellSlots A N R)) Cold,
        Nat.card (PhysicalFamily
          (wordParameter (cellSlots A N R) - binSupport b.1)
          b.1.1.1 b.1.1.2
          (Fin (2 * wordParameter (cellSlots A N R)))) := by
  simpa using sourceCode_card_le_bound_mul_sum A N R hnoncritical Q
    (fixedCellSourceCode A N R Cold)

/-! ## The sole remaining ambient-cell interface -/

/-- An actual residual family enters one fixed product/axis/route cell.
`Decoration` contains only data not recoverable from the exact-axis subgroup,
for example a bounded chart or route tie-breaker.  The routes themselves are
fixed by `R` and are not elements of the decoration. -/
structure AmbientCellCode (Actual : Type*) where
  Decoration : Type
  decorationFinite : Finite Decoration
  decoration : Actual → Decoration
  fixedCell : Actual → FixedCell A N
  joint_injective :
    Function.Injective (fun H ↦ (decoration H, fixedCell H))

/-- Existing routed exact-axis injectivity turns an ambient cell code into
the precise word-source code required by the physical producer. -/
def AmbientCellCode.toSourceCode {Actual : Type*}
    (C : AmbientCellCode A N Actual) {Cold K : ℕ}
    (hcard : Nat.card C.Decoration ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold))) :
    SourceCode (cellSlots A N R) Actual Cold K where
  Decoration := C.Decoration
  decorationFinite := C.decorationFinite
  decoration := C.decoration
  word := fun H ↦ routedSource A N R (C.fixedCell H)
  joint_injective := by
    intro H H' h
    have hdecoration : C.decoration H = C.decoration H' :=
      congrArg (fun z : C.Decoration × WordSource (cellSlots A N R) ↦ z.1) h
    have hword :
        routedSource A N R (C.fixedCell H) =
          routedSource A N R (C.fixedCell H') :=
      congrArg (fun z : C.Decoration × WordSource (cellSlots A N R) ↦ z.2) h
    apply C.joint_injective
    apply Prod.ext
    · exact hdecoration
    · apply routedSource_injective A N R
      exact hword
  decoration_card_le := hcard

/-- Symbolic ambient-cell theorem.  Once the genuinely unrecoverable chart
data have cardinality at most `B`, it suffices to absorb that single `B` into
the standard decoration budget. -/
theorem ambientCell_card_le_bound_mul_sum
    {Actual : Type*} [Finite Actual] {Cold K B : ℕ}
    (hnoncritical : ∃ c : Σ i, cells (cellSlots A N R) i,
      ∃ t, colors (cellSlots A N R) c = .inr t)
    (Q : Retention (cellSlots A N R) Cold)
    (C : AmbientCellCode A N Actual)
    (hdecoration : Nat.card C.Decoration ≤ B)
    (hB : B ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold))) :
    Nat.card Actual ≤
      (2 * wordParameter (cellSlots A N R) + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin (wordParameter (cellSlots A N R)) Cold,
          Nat.card (PhysicalFamily
            (wordParameter (cellSlots A N R) - binSupport b.1)
            b.1.1.1 b.1.1.2
            (Fin (2 * wordParameter (cellSlots A N R)))) :=
  sourceCode_card_le_bound_mul_sum A N R hnoncritical Q
    (AmbientCellCode.toSourceCode A N R C (hdecoration.trans hB))

/-! ## Fixed ambient product charts -/

/-- Actual ambient subgroups lying in one fixed product-action range and
having the prescribed full projections and literal normal axes after comap.
This is the canonical fixed-chart residual cell. -/
abbrev FixedAmbientFamily {G : Type*} [Group G]
    (phi : (∀ i, A i) →* G) :=
  {H : Subgroup G //
    H ≤ phi.range ∧
      CarrierProductFull (H.comap phi) ∧
        ∀ i, carrierAxis (H.comap phi) i = N i}

/-- Comap along the fixed product-action chart produces the exact-axis
product subgroup consumed by `routedSource`. -/
def fixedAmbientCell {G : Type*} [Group G]
    (phi : (∀ i, A i) →* G) :
    FixedAmbientFamily A N phi → FixedCell A N :=
  fun H ↦ ⟨H.1.comap phi, H.2.2.1, H.2.2.2⟩

/-- The actual ambient subgroup is recovered by mapping its comap back along
the fixed chart.  Injectivity does not require the chart homomorphism itself
to be injective. -/
theorem fixedAmbientCell_injective {G : Type*} [Group G]
    (phi : (∀ i, A i) →* G) :
    Function.Injective (fixedAmbientCell A N phi) := by
  intro H K h
  apply Subtype.ext
  have hcomap : H.1.comap phi = K.1.comap phi :=
    congrArg (fun L : FixedCell A N ↦ L.1) h
  rw [← Subgroup.map_comap_eq_self H.2.1,
    ← Subgroup.map_comap_eq_self K.2.1, hcomap]

/-- A fixed ambient product chart needs no decoration.  All axis and route
data are fixed by the cell, and the actual subgroup is recovered from its
comap. -/
def fixedAmbientCellCode {G : Type*} [Group G]
    (phi : (∀ i, A i) →* G) :
    AmbientCellCode A N (FixedAmbientFamily A N phi) where
  Decoration := PUnit
  decorationFinite := inferInstance
  decoration := fun _ ↦ PUnit.unit
  fixedCell := fixedAmbientCell A N phi
  joint_injective := by
    intro H K h
    apply fixedAmbientCell_injective A N phi
    exact congrArg Prod.snd h

/-- The complete actual-to-word source code on one fixed ambient chart. -/
def fixedAmbientSourceCode {G : Type*} [Group G]
    (phi : (∀ i, A i) →* G) (Cold : ℕ) :
    SourceCode (cellSlots A N R) (FixedAmbientFamily A N phi) Cold 0 :=
  AmbientCellCode.toSourceCode A N R (fixedAmbientCellCode A N phi) (by
    simp [fixedAmbientCellCode])

/-- Exact retained-bin count on a fixed ambient product chart.  This is an
actual subgroup family, and it still carries no decoration factor. -/
theorem fixedAmbientFamily_card_le_sum
    {G : Type*} [Group G] [Finite G]
    (phi : (∀ i, A i) →* G) {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells (cellSlots A N R) i,
      ∃ t, colors (cellSlots A N R) c = .inr t)
    (Q : Retention (cellSlots A N R) Cold) :
    Nat.card (FixedAmbientFamily A N phi) ≤
      ∑ b : RetainedBin (wordParameter (cellSlots A N R)) Cold,
        Nat.card (PhysicalFamily
          (wordParameter (cellSlots A N R) - binSupport b.1)
          b.1.1.1 b.1.1.2
          (Fin (2 * wordParameter (cellSlots A N R)))) := by
  simpa using sourceCode_card_le_bound_mul_sum A N R hnoncritical Q
    (fixedAmbientSourceCode A N R phi Cold)

end SymmetricSubgroupAsymptotics.BinaryCarrierActualRoutedSourceCode
