import SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer

/-!
# A canonical finite alphabet for carrier decorations

The physical reconstruction theorem needs a decoration space of cardinality
at most `(2*N+2)^(K*(2*Cold))`.  This file makes that numerical obligation
literal: a decoration is a word of the permitted length over the permitted
alphabet.  A producer therefore only has to construct its encoding and prove
joint injectivity with the reversible carrier word; the cardinal estimate is
automatic.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDecorationCode

open BinaryCarrierActualDecoratedTransport
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierParameterProfiles

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- The canonical decoration budget: one alphabet symbol for each of
`K*(2*Cold)` reconstruction slots. -/
abbrev DecorationCode (N Cold K : ℕ) :=
  Fin (K * (2 * Cold)) → Fin (2 * N + 2)

theorem decorationCode_card (N Cold K : ℕ) :
    Nat.card (DecorationCode N Cold K) =
      (2 * N + 2) ^ (K * (2 * Cold)) := by
  rw [Nat.card_fun,Nat.card_fin,Nat.card_fin]

variable {iota : Type*} [Fintype iota] [DecidableEq iota]
  (slot : iota → BinaryCarrierWordClosure.Slot)

/-- Install an explicit bounded decoration word and a reversible word-source
code as the producer's `SourceCode`. -/
def ofBoundedEncoding {Actual : Type*} {Cold K : ℕ}
    (decoration : Actual → DecorationCode (wordParameter slot) Cold K)
    (word : Actual → WordSource slot)
    (joint_injective : Function.Injective (fun H ↦ (decoration H, word H))) :
    SourceCode slot Actual Cold K where
  Decoration := DecorationCode (wordParameter slot) Cold K
  decorationFinite := inferInstance
  decoration := decoration
  word := word
  joint_injective := joint_injective
  decoration_card_le := (decorationCode_card (wordParameter slot) Cold K).le

/-- The complete retained-bin cardinal estimate for any finite actual source
equipped with a bounded encoding and a reversible word-source code. -/
theorem card_le_bound_mul_sum {Actual : Type*} [Finite Actual]
    {Cold K : ℕ}
    (hnoncritical : ∃ c : Σ i, BinaryCarrierWordClosure.cells slot i,
      ∃ t, BinaryCarrierWordClosure.colors slot c = .inr t)
    (R : Retention slot Cold)
    (decoration : Actual → DecorationCode (wordParameter slot) Cold K)
    (word : Actual → WordSource slot)
    (joint_injective : Function.Injective (fun H ↦ (decoration H, word H))) :
    Nat.card Actual ≤
      (2 * wordParameter slot + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin (wordParameter slot) Cold,
          Nat.card (PhysicalFamily
            (wordParameter slot - binSupport b.1)
            b.1.1.1 b.1.1.2 (Fin (2 * wordParameter slot))) := by
  let f : Actual →
      DecorationCode (wordParameter slot) Cold K ×
        Target (wordParameter slot) Cold :=
    fun H ↦ (decoration H, wordTarget slot hnoncritical R (word H))
  have hf : Function.Injective f := by
    intro H H' h
    have hdecoration : decoration H = decoration H' :=
      congrArg (fun z : DecorationCode (wordParameter slot) Cold K ×
        Target (wordParameter slot) Cold ↦ z.1) h
    have htarget : wordTarget slot hnoncritical R (word H) =
        wordTarget slot hnoncritical R (word H') :=
      congrArg (fun z : DecorationCode (wordParameter slot) Cold K ×
        Target (wordParameter slot) Cold ↦ z.2) h
    have hword : word H = word H' :=
      wordTarget_injective slot hnoncritical R htarget
    exact joint_injective (Prod.ext hdecoration hword)
  calc
    Nat.card Actual ≤ Nat.card
        (DecorationCode (wordParameter slot) Cold K ×
          Target (wordParameter slot) Cold) :=
      Nat.card_le_card_of_injective f hf
    _ = Nat.card (DecorationCode (wordParameter slot) Cold K) *
        Nat.card (Target (wordParameter slot) Cold) := Nat.card_prod _ _
    _ = (2 * wordParameter slot + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin (wordParameter slot) Cold,
          Nat.card (PhysicalFamily
            (wordParameter slot - binSupport b.1)
            b.1.1.1 b.1.1.2 (Fin (2 * wordParameter slot))) := by
      rw [decorationCode_card,
        BinaryCarrierActualDecoratedTransport.Transport.target_card_eq_sum]

end SymmetricSubgroupAsymptotics.BinaryCarrierDecorationCode
