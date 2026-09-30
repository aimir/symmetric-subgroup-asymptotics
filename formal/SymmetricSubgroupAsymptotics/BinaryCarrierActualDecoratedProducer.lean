import SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedTransport
import SymmetricSubgroupAsymptotics.BinaryCarrierWordClosure

/-!
# Generic physical producer for actual decorated binary transport

The heterogeneous carrier `Slot` is already the correct local reversible
object: its displayed carrier may be a nonabelian proper subdirect subgroup,
and a quotient-identity slot is simply another value of the same type.  This
file composes a whole word of such slots with an actual-source reconstruction
code.

The only counted auxiliary datum is one uniformly bounded decoration.  The
slot word is not counted: it is fixed on the source cell.  Its reversible
transport lands in one literal physical `(a,T)` bin, and the bin is retained
in the target sigma type.  Thus no profile witness or carrier-route witness is
introduced into the target cardinality.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer

open BinaryCarrierActualDecoratedTransport
open BinaryCarrierCellProfile
open BinaryCarrierParameterProfiles
open BinaryCarrierParameterUnion
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G ↦ (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (slot : ι → Slot)

/-- The exact half-degree of the physical word produced by the displayed
slot cells. -/
abbrev wordParameter : ℕ :=
  parameter (cells slot) (colors slot)

/-- The noncritical half-support retained by the displayed slot cells. -/
abbrev wordSupport : ℕ :=
  2 * cyclicMultiplicity (cells slot) (colors slot) +
    4 * carrierScale (cells slot) (colors slot)

theorem wordParameter_sub_wordSupport :
    wordParameter slot - wordSupport slot =
      criticalRank (cells slot) (colors slot) := by
  unfold wordParameter wordSupport parameter
  omega

/-- The complete reversible source relation for the fixed slot word. -/
abbrev WordSource :=
  CarrierTransportSource (alphas slot)

/-- Per-slot support accounting.  The local producer records how much old
carrier support belongs to each slot and how much that slot retains.  The two
sum identities connect this local accounting to the actual source cell and
to the canonical physical profile read from the displayed colours. -/
structure Retention (Cold : ℕ) where
  oldSupport : ι → ℕ
  retainedSupport : ι → ℕ
  old_sum : ∑ i, oldSupport i = Cold
  retained_sum : ∑ i, retainedSupport i = wordSupport slot
  retained_le_old : ∀ i, retainedSupport i ≤ oldSupport i
  old_le_four_retained : ∀ i, oldSupport i ≤ 4 * retainedSupport i

namespace Retention

variable {slot}

theorem wordSupport_le {Cold : ℕ} (R : Retention slot Cold) :
    wordSupport slot ≤ Cold := by
  calc
    wordSupport slot = ∑ i, R.retainedSupport i := R.retained_sum.symm
    _ ≤ ∑ i, R.oldSupport i :=
      Finset.sum_le_sum (fun i _ ↦ R.retained_le_old i)
    _ = Cold := R.old_sum

theorem oldSupport_le_four_wordSupport {Cold : ℕ}
    (R : Retention slot Cold) :
    Cold ≤ 4 * wordSupport slot := by
  calc
    Cold = ∑ i, R.oldSupport i := R.old_sum.symm
    _ ≤ ∑ i, 4 * R.retainedSupport i :=
      Finset.sum_le_sum (fun i _ ↦ R.old_le_four_retained i)
    _ = 4 * ∑ i, R.retainedSupport i := by
      rw [Finset.mul_sum]
    _ = 4 * wordSupport slot := by rw [R.retained_sum]

end Retention

/-- The exact fixed-bin physical transport associated to an arbitrary word
of reversible slots.  The underlying `Slot.carrier` is never enlarged to the
product of its projections. -/
def physicalWordTransport :
    WordSource slot →
      PhysicalFamily
        (criticalRank (cells slot) (colors slot))
        (cyclicMultiplicity (cells slot) (colors slot))
        (carrierScale (cells slot) (colors slot))
        (Fin (2 * wordParameter slot)) :=
  physicalTransport
    (C := carriers slot)
    (hC := fun i ↦ (slot i).carrierFull)
    (α := alphas slot)
    (β := betas slot)
    (hα := fun i ↦ (slot i).alphaSurjective)
    (hβ := fun i ↦ (slot i).betaSurjective)
    (s := index (cells slot) (colors slot))
    (Dmix := originalColorDisplay (cells slot) (colors slot))

theorem physicalWordTransport_injective :
    Function.Injective (physicalWordTransport slot) :=
  physicalTransport_injective
    (C := carriers slot)
    (hC := fun i ↦ (slot i).carrierFull)
    (α := alphas slot)
    (β := betas slot)
    (hα := fun i ↦ (slot i).alphaSurjective)
    (hβ := fun i ↦ (slot i).betaSurjective)
    (s := index (cells slot) (colors slot))
    (Dmix := originalColorDisplay (cells slot) (colors slot))

/-- The canonical retained bin of the word.  Its positivity is supplied by
one displayed noncritical cell; its two support inequalities are aggregated
from the per-slot retention certificate. -/
def retainedWordBin {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i, ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold) :
    RetainedBin (wordParameter slot) Cold := by
  refine ⟨⟨(cyclicMultiplicity (cells slot) (colors slot),
      carrierScale (cells slot) (colors slot)), ?_⟩, ?_, ?_⟩
  · rw [mem_bins]
    refine ⟨support_pos_of_noncritical (cells slot) (colors slot) hnoncritical,
      ?_, True.intro⟩
    change wordSupport slot ≤ wordParameter slot
    unfold wordSupport wordParameter parameter
    omega
  · change wordSupport slot ≤ Cold
    exact R.wordSupport_le
  · change Cold ≤ 4 * wordSupport slot
    exact R.oldSupport_le_four_wordSupport

@[simp] theorem retainedWordBin_support {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i, ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold) :
    binSupport (retainedWordBin slot hnoncritical R).1 = wordSupport slot :=
  rfl

/-- Embed the reversible word source into the actual retained-bin target.
The sigma index is fixed, while the second component is the actual physical
subgroup produced by simultaneous carrier transport. -/
theorem wordFamilyType_eq :
    PhysicalFamily
        (criticalRank (cells slot) (colors slot))
        (cyclicMultiplicity (cells slot) (colors slot))
        (carrierScale (cells slot) (colors slot))
        (Fin (2 * wordParameter slot)) =
      PhysicalFamily
        (wordParameter slot - wordSupport slot)
        (cyclicMultiplicity (cells slot) (colors slot))
        (carrierScale (cells slot) (colors slot))
        (Fin (2 * wordParameter slot)) :=
  congrArg
    (fun R ↦ PhysicalFamily R
      (cyclicMultiplicity (cells slot) (colors slot))
      (carrierScale (cells slot) (colors slot))
      (Fin (2 * wordParameter slot)))
    (wordParameter_sub_wordSupport slot).symm

def wordPhysicalTarget : WordSource slot →
    PhysicalFamily
      (wordParameter slot - wordSupport slot)
      (cyclicMultiplicity (cells slot) (colors slot))
      (carrierScale (cells slot) (colors slot))
      (Fin (2 * wordParameter slot)) :=
  fun H ↦ cast (wordFamilyType_eq slot) (physicalWordTransport slot H)

theorem wordPhysicalTarget_injective :
    Function.Injective (wordPhysicalTarget slot) :=
  (cast_bijective (wordFamilyType_eq slot)).injective.comp
    (physicalWordTransport_injective slot)

def wordTarget {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i, ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold) :
    WordSource slot → Target (wordParameter slot) Cold :=
  fun H ↦ ⟨retainedWordBin slot hnoncritical R, wordPhysicalTarget slot H⟩

theorem wordTarget_injective {Cold : ℕ}
    (hnoncritical : ∃ c : Σ i, cells slot i, ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold) :
    Function.Injective (wordTarget slot hnoncritical R) := by
  intro H H' h
  apply wordPhysicalTarget_injective slot
  exact (@sigma_mk_injective
    (RetainedBin (wordParameter slot) Cold)
    (fun b ↦ PhysicalFamily
      (wordParameter slot - binSupport b.1)
      b.1.1.1 b.1.1.2 (Fin (2 * wordParameter slot)))
    (retainedWordBin slot hnoncritical R)) h

/-- The remaining source-side obligation.  Each actual residual subgroup is
coded by one bounded decoration and one reversible word-source relation.
Joint injectivity is sufficient: neither projection must be injective alone. -/
structure SourceCode (Actual : Type*) (Cold K : ℕ) where
  Decoration : Type
  decorationFinite : Finite Decoration
  decoration : Actual → Decoration
  word : Actual → WordSource slot
  joint_injective :
    Function.Injective (fun H ↦ (decoration H, word H))
  decoration_card_le :
    Nat.card Decoration ≤
      (2 * wordParameter slot + 2) ^ (K * (2 * Cold))

/-- Compose a source reconstruction code with the simultaneous reversible
slot transport.  This is the generic actual decorated physical producer. -/
def toTransport {Cold K : ℕ}
    {Residual : Subgroup (Equiv.Perm (Fin (2 * wordParameter slot))) → Prop}
    (hnoncritical : ∃ c : Σ i, cells slot i, ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold)
    (E : SourceCode slot (Source (wordParameter slot) Residual) Cold K) :
    Transport (wordParameter slot) Cold K Residual where
  Decoration := E.Decoration
  decorationFinite := E.decorationFinite
  decoration := E.decoration
  target := fun H ↦ wordTarget slot hnoncritical R (E.word H)
  joint_injective := by
    intro H H' h
    have hdecoration : E.decoration H = E.decoration H' :=
      congrArg (fun z : E.Decoration × Target (wordParameter slot) Cold ↦ z.1) h
    have htarget :
        wordTarget slot hnoncritical R (E.word H) =
          wordTarget slot hnoncritical R (E.word H') :=
      congrArg (fun z : E.Decoration × Target (wordParameter slot) Cold ↦ z.2) h
    have hword : E.word H = E.word H' :=
      wordTarget_injective slot hnoncritical R htarget
    exact E.joint_injective (Prod.ext hdecoration hword)
  decoration_card_le := E.decoration_card_le

/-- Cardinality consequence in the exact retained-bin form used by the
original-weight numerical estimates. -/
theorem actualSource_card_le_bound_mul_sum {Cold K : ℕ}
    {Residual : Subgroup (Equiv.Perm (Fin (2 * wordParameter slot))) → Prop}
    (hnoncritical : ∃ c : Σ i, cells slot i, ∃ t, colors slot c = .inr t)
    (R : Retention slot Cold)
    (E : SourceCode slot (Source (wordParameter slot) Residual) Cold K) :
    Nat.card (Source (wordParameter slot) Residual) ≤
      (2 * wordParameter slot + 2) ^ (K * (2 * Cold)) *
        ∑ b : RetainedBin (wordParameter slot) Cold,
          Nat.card (PhysicalFamily
            (wordParameter slot - binSupport b.1)
            b.1.1.1 b.1.1.2 (Fin (2 * wordParameter slot))) :=
  (toTransport slot hnoncritical R E).source_card_le_bound_mul_sum

end SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer
