import SymmetricSubgroupAsymptotics.BinaryCarrierActualRoutedSourceCode

/-!
# Bounded dependent variable-word carrier producer

This is the profile-free aggregation interface for actual carrier sources.
The bounded decoration determines an entire heterogeneous word of reversible
`Slot`s, including its finite coordinate type.  Different decorations may
therefore carry different action groups, normal axes, routes, and numbers of
coordinates.

Every decorated word has the same half-degree `N`, has a noncritical cell,
and carries a retention certificate against the same old support `Cold`.
Consequently every dependent `WordSource` lands in the one common
`Target N Cold`.  Equality in the decorated target first identifies the
decoration, hence the dependent word; `wordTarget_injective` then identifies
the word source.  No sigma over raw profiles occurs in the cardinal bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDependentVariableWordProducer

open BinaryCarrierActualDecoratedProducer
open BinaryCarrierActualDecoratedTransport
open BinaryCarrierParameterProfiles
open BinaryCarrierRoutedWordClosure
open BinaryCarrierWordClosure
open BinaryDegreeEightPhysicalAnalyticClosure

attribute [local instance] Fintype.ofFinite

/-! ## Decoration-determined heterogeneous slot words -/

/-- A heterogeneous slot word with its coordinate type bundled.  Bundling the
coordinate type is what permits different decorations to have different
orbit multiplicities without first partitioning the source by a fixed
profile. -/
structure SlotWord where
  Index : Type
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  slot : Index → Slot

namespace SlotWord

/-- Half-degree of the physical word. -/
def parameter (W : SlotWord) : ℕ := by
  letI : Fintype W.Index := W.indexFintype
  letI : DecidableEq W.Index := W.indexDecidableEq
  exact wordParameter W.slot

/-- Noncritical half-support displayed by the word. -/
def support (W : SlotWord) : ℕ := by
  letI : Fintype W.Index := W.indexFintype
  letI : DecidableEq W.Index := W.indexDecidableEq
  exact wordSupport W.slot

/-- The complete reversible source relation for this dependent word. -/
abbrev Source (W : SlotWord) : Type := by
  letI : Fintype W.Index := W.indexFintype
  letI : DecidableEq W.Index := W.indexDecidableEq
  exact WordSource W.slot

/-- At least one displayed cell of the word is noncritical. -/
def HasNoncritical (W : SlotWord) : Prop := by
  letI : Fintype W.Index := W.indexFintype
  letI : DecidableEq W.Index := W.indexDecidableEq
  exact ∃ c : Σ i, cells W.slot i, ∃ t, colors W.slot c = .inr t

/-- The per-slot old and retained support certificate for this word. -/
abbrev RetentionAt (W : SlotWord) (Cold : ℕ) : Type := by
  letI : Fintype W.Index := W.indexFintype
  letI : DecidableEq W.Index := W.indexDecidableEq
  exact Retention W.slot Cold

end SlotWord

/-- A heterogeneous slot word ready to land in the common retained-bin target.
The source type and its target injection are cached as fields.  This keeps the
dependent aggregation opaque: Lean need not repeatedly normalize the large
`WordSource` type while comparing two decorations. -/
structure RoutedWord (N Cold : ℕ) where
  word : SlotWord
  Source : Type
  target : Source → Target N Cold
  target_injective : Function.Injective target
  support : ℕ
  support_le_old : support ≤ Cold
  old_le_four_support : Cold ≤ 4 * support

namespace RoutedWord

variable {N Cold : ℕ}

/-- Build the cached interface from an actual heterogeneous slot word.  The
large dependent type is normalized once here and stays opaque in the
profile-free cardinal argument. -/
def ofSlotWord (W : SlotWord)
    (parameter_eq : W.parameter = N)
    (noncritical : W.HasNoncritical)
    (retention : W.RetentionAt Cold) : RoutedWord N Cold := by
  letI : Fintype W.Index := W.indexFintype
  letI : DecidableEq W.Index := W.indexDecidableEq
  let f : W.Source → Target N Cold := fun H =>
    cast (congrArg (fun M ↦ Target M Cold) parameter_eq)
      (wordTarget W.slot noncritical retention H)
  refine {
    word := W
    Source := W.Source
    target := f
    target_injective := ?_
    support := W.support
    support_le_old := retention.wordSupport_le
    old_le_four_support := retention.oldSupport_le_four_wordSupport }
  exact
    (cast_bijective
      (congrArg (fun M ↦ Target M Cold) parameter_eq)).injective.comp
      (wordTarget_injective W.slot noncritical retention)

end RoutedWord

/-! ## Dependent source codes -/

/-- A bounded decoration determines the complete routed word.  The actual
object is encoded in the dependent sum of that decoration and the appropriate
word source.  Thus `code_injective` is the sole physical reconstruction
obligation; the generic producer handles all dependent transports after it. -/
structure Code (Actual : Type*) (N Cold K : ℕ) where
  Decoration : Type
  decorationFinite : Finite Decoration
  routedWord : Decoration → RoutedWord N Cold
  code : Actual → Σ d : Decoration, (routedWord d).Source
  code_injective : Function.Injective code
  decoration_card_le :
    Nat.card Decoration ≤ (2 * N + 2) ^ (K * (2 * Cold))

namespace Code

variable {Actual : Type*} {N Cold K : ℕ}
  (E : Code Actual N Cold K)

/-- Send a dependent word source to its decoration and the common physical
target. -/
def dependentTarget :
    (Σ d : E.Decoration, (E.routedWord d).Source) →
      E.Decoration × Target N Cold
  | ⟨d,H⟩ => ⟨d,(E.routedWord d).target H⟩

/-- Equality of decorations aligns the dependent word types.  Injectivity of
the corresponding `wordTarget` then recovers the source. -/
theorem dependentTarget_injective : Function.Injective E.dependentTarget := by
  rintro ⟨d,H⟩ ⟨d',H'⟩ h
  have hd : d = d' :=
    congrArg (fun z : E.Decoration × Target N Cold ↦ z.1) h
  subst d'
  have ht : (E.routedWord d).target H = (E.routedWord d).target H' :=
    congrArg (fun z : E.Decoration × Target N Cold ↦ z.2) h
  have hH : H = H' := (E.routedWord d).target_injective ht
  cases hH
  rfl

/-- The actual source map into bounded decoration times the common retained
physical target. -/
def encodedTarget : Actual → E.Decoration × Target N Cold :=
  E.dependentTarget ∘ E.code

theorem encodedTarget_injective : Function.Injective E.encodedTarget :=
  E.dependentTarget_injective.comp E.code_injective

/-- Generic cardinal consequence.  There is one bounded decoration factor
and the exact common retained-bin sum; no raw action, axis, or route profile
sum is introduced. -/
theorem card_le_bound_mul_sum [Finite Actual]
    (E : Code Actual N Cold K) :
    Nat.card Actual ≤
      (2 * N + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin N Cold,
          Nat.card (PhysicalFamily
            (N - binSupport b.1) b.1.1.1 b.1.1.2 (Fin (2 * N))) := by
  letI : Finite E.Decoration := E.decorationFinite
  calc
    Nat.card Actual ≤ Nat.card (E.Decoration × Target N Cold) :=
      Nat.card_le_card_of_injective E.encodedTarget E.encodedTarget_injective
    _ = Nat.card E.Decoration * Nat.card (Target N Cold) :=
      Nat.card_prod _ _
    _ ≤ (2 * N + 2) ^ (K * (2 * Cold)) * Nat.card (Target N Cold) :=
      Nat.mul_le_mul_right _ E.decoration_card_le
    _ = _ := by rw [Nat.card_sigma]

/-- Specialize a dependent variable-word code on an actual residual subgroup
family to the existing physical `Transport` interface. -/
def toTransport
    {Residual : Subgroup (Equiv.Perm (Fin (2 * N))) → Prop}
    (E : Code (Source N Residual) N Cold K) :
    Transport N Cold K Residual where
  Decoration := E.Decoration
  decorationFinite := E.decorationFinite
  decoration := fun H ↦ (E.encodedTarget H).1
  target := fun H ↦ (E.encodedTarget H).2
  joint_injective := by
    intro H H' h
    apply E.encodedTarget_injective
    apply Prod.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  decoration_card_le := E.decoration_card_le

end Code

end SymmetricSubgroupAsymptotics.BinaryCarrierDependentVariableWordProducer
