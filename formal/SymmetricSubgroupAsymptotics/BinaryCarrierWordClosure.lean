import SymmetricSubgroupAsymptotics.BinaryCarrierCellProfile

/-!
# Whole-word closure for simultaneous original-action carriers

A finite carrier word consists of literal proper carrier subgroups whose
displayed cells are coloured by the completed original-action alphabet.  If
each carrier is full on every displayed cell and shares a surjective quotient
with its source coordinate, reversible transport sends the entire decorated
source family injectively into one exact completed-mixture family.

The theorem is simultaneous: internal relations inside every proper carrier
and quotient relations between all source coordinates are retained.  The
target pays no carrier, chart, quotient, axis, or occurrence marking.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWordClosure

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierCellProfile

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (κ : ι → Type*) [∀ i, Fintype (κ i)]
  (color : Cell κ → Kind)
  {U Q : ι → Type*} [∀ i, Group (U i)] [∀ i, Group (Q i)]
  [∀ i, Finite (U i)]

/-- The literal proper carrier displayed at source coordinate `i`. -/
abbrev CarrierWord :=
  ∀ i, Subgroup (∀ j, mixtureAction (color ⟨i,j⟩))

variable (C : CarrierWord κ color)
  (hC : ∀ i, CarrierProductFull (C i))
  (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
  (hα : ∀ i, Function.Surjective (α i))
  (hβ : ∀ i, Function.Surjective (β i))
  (hnoncritical : ∃ c : Cell κ, ∃ t, color c = .inr t)

/-- The degree parameter occupied by all displayed original-action cells. -/
abbrev parameter : ℕ :=
  criticalRank κ color +
    2*cyclicMultiplicity κ color + 4*carrierScale κ color

/-- Reversible simultaneous transport into the exact completed mixture
selected canonically by the colours of the displayed cells. -/
def transport :
    CarrierTransportSource α →
      BinaryCarrierMixtureCompletion.Family (parameter κ color) :=
  mixtureTransport
    (C := C) (hC := hC) (α := α) (β := β)
    (hα := hα) (hβ := hβ)
    (s := index κ color) (Dmix := originalColorDisplay κ color)
    (support_pos_of_noncritical κ color hnoncritical)

/-- The whole-word transport is reversible. -/
theorem transport_injective :
    Function.Injective
      (transport κ color C hC α β hα hβ hnoncritical) :=
  mixtureTransport_injective
    (C := C) (hC := hC) (α := α) (β := β)
    (hα := hα) (hβ := hβ)
    (s := index κ color) (Dmix := originalColorDisplay κ color)
    (support_pos_of_noncritical κ color hnoncritical)

include C hC β hα hβ hnoncritical in
/-- Every fixed simultaneous carrier word is absorbed by the already proved
negligible completed mixture, with all original quotient and axis data
recovered by the injection. -/
theorem source_card_le_mixture :
    Nat.card (CarrierTransportSource α) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family (parameter κ color)) :=
  Nat.card_le_card_of_injective _
    (transport_injective κ color C hC α β hα hβ hnoncritical)

/-! ## Bundled heterogeneous carrier words -/

/-- One local reversible carrier slot, including its literal displayed cells,
original-action colours, common quotient maps, and fullness certificate.  The
source and quotient groups may vary from slot to slot. -/
structure Slot where
  Cells : Type*
  Source : Type*
  Quotient : Type*
  cellsFintype : Fintype Cells
  sourceGroup : Group Source
  quotientGroup : Group Quotient
  sourceFinite : Finite Source
  color : Cells → Kind
  carrier : Subgroup (∀ j, mixtureAction (color j))
  carrierFull : CarrierProductFull carrier
  alpha : Source →* Quotient
  beta : carrier →* Quotient
  alphaSurjective : Function.Surjective alpha
  betaSurjective : Function.Surjective beta

attribute [instance] Slot.cellsFintype Slot.sourceGroup Slot.quotientGroup
  Slot.sourceFinite

section Bundled

variable {δ : Type*} [Fintype δ] [DecidableEq δ] (slot : δ → Slot)

abbrev cells (i : δ) := (slot i).Cells
abbrev colors (c : Σ i, cells slot i) : Kind := (slot c.1).color c.2
abbrev sources (i : δ) := (slot i).Source
abbrev quotients (i : δ) := (slot i).Quotient
abbrev carriers (i : δ) :
    Subgroup (∀ j, mixtureAction (colors slot ⟨i,j⟩)) := (slot i).carrier
abbrev alphas (i : δ) : sources slot i →* quotients slot i := (slot i).alpha
abbrev betas (i : δ) : carriers slot i →* quotients slot i := (slot i).beta

/-- A heterogeneous finite word of bundled local slots satisfies the same
marking-free completed-mixture bound. -/
theorem slot_source_card_le_mixture
    (hnoncritical : ∃ c : Σ i, cells slot i, ∃ t,
      colors slot c = .inr t) :
    Nat.card (CarrierTransportSource (alphas slot)) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter (cells slot) (colors slot))) :=
  source_card_le_mixture
    (κ := cells slot) (color := colors slot)
    (C := carriers slot) (hC := fun i => (slot i).carrierFull)
    (α := alphas slot) (β := betas slot)
    (hα := fun i => (slot i).alphaSurjective)
    (hβ := fun i => (slot i).betaSurjective)
    hnoncritical

end Bundled

end SymmetricSubgroupAsymptotics.BinaryCarrierWordClosure
