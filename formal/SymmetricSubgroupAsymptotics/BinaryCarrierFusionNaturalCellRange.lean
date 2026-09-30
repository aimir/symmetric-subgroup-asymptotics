import SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalPointChart

/-!
# Literal-cell ranges in a fusion-natural point chart

The fusion-natural chart is assembled in two stages: the canonical mixture
profile is reindexed by the literal displayed cells of the word, and the
displayed cells are then assembled onto the ambient point set.  This file
records the pointwise computation, including the otherwise hidden canonical
occurrence number of a literal cell.

The range corollary is the form used by orbit reconstruction.  Its left side
is one honest occurrence block of the completed mixture profile, so it can be
inserted directly in `orbit_eq_block_of_transitive`; its right side is the
literal assembled range of the selected slot cell.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalCellRange

open SymmetricSubgroupAsymptotics
open BinaryCarrierCellProfile
open BinaryCarrierFusionNaturalPointChart
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  (slot : ι → Slot)

/-- The exact completed-mixture multiplicity selected by the displayed
cells of a carrier word. -/
abbrev selectedMultiplicity :=
  profileMultiplicity
    (criticalRank (cells slot) (colors slot))
    (cyclicMultiplicity (cells slot) (colors slot))
    (carrierScale (cells slot) (colors slot))
    (index (cells slot) (colors slot))

/-- The canonical occurrence number occupied by a literal displayed cell.
The only transport changes the cell-fibre multiplicity into the definitionally
equal completed-profile multiplicity. -/
def literalOccurrenceIndex (i : ι) (c : (slot i).Cells) :
    Fin (selectedMultiplicity slot (colors slot ⟨i,c⟩)) :=
  Equiv.cast
    (congrArg Fin (congrFun
      (indexed_multiplicity (cells slot) (colors slot))
      (colors slot ⟨i,c⟩)).symm)
    (Fintype.equivFin
      (fiber (cells slot) (colors slot) (colors slot ⟨i,c⟩))
      ⟨⟨i,c⟩,rfl⟩)

/-- The prefix of the fusion-natural point chart which forgets the canonical
profile enumeration and returns to literal displayed cells.  It is stated
with an explicit multiplicity equality so its action on the corresponding
fibre can be computed by equality induction. -/
private def literalCellReindex
    {m : Kind → ℕ}
    (h : m = multiplicity (cells slot) (colors slot)) :
    OrbitProfilePoints mixturePoints m ≃
      (Σ i, Σ c : cells slot i, mixturePoints (colors slot ⟨i,c⟩)) :=
  (Equiv.cast (congrArg (OrbitProfilePoints mixturePoints) h)).trans
    ((profilePointEquivOccurrencePoint mixturePoints
      (multiplicity (cells slot) (colors slot))).trans
    ((occurrencePointEquivCellPoint slot).trans
      (Equiv.sigmaAssoc (fun i c ↦
        mixturePoints (colors slot ⟨i,c⟩)))))

/-- Equality induction through the canonical colour-fibre enumeration: the
profile point at the occurrence belonging to a displayed cell is sent to
that very literal cell, with its local point unchanged. -/
private theorem literalCellReindex_apply
    {m : Kind → ℕ}
    (h : m = multiplicity (cells slot) (colors slot))
    (i : ι) (c : (slot i).Cells)
    (x : mixturePoints (colors slot ⟨i,c⟩)) :
    literalCellReindex slot h
        ⟨colors slot ⟨i,c⟩,
          Equiv.cast
            (congrArg Fin (congrFun h (colors slot ⟨i,c⟩)).symm)
            (Fintype.equivFin
              (fiber (cells slot) (colors slot) (colors slot ⟨i,c⟩))
              ⟨⟨i,c⟩,rfl⟩),
          x⟩ =
      ⟨i,⟨c,x⟩⟩ := by
  cases h
  have hpoint :
      occurrencePointEquivCellPoint slot
          ⟨⟨colors slot ⟨i,c⟩,
              Fintype.equivFin
                (fiber (cells slot) (colors slot) (colors slot ⟨i,c⟩))
                ⟨⟨i,c⟩,rfl⟩⟩,x⟩ =
        ⟨⟨i,c⟩,x⟩ := by
    apply Sigma.ext
    · exact (occurrenceToCell (cells slot) (colors slot)).apply_symm_apply
        ⟨i,c⟩
    · simp [occurrencePointEquivCellPoint, Equiv.sigmaCongr]
  change (Equiv.sigmaAssoc (fun i c ↦
      mixturePoints (colors slot ⟨i,c⟩)))
      (occurrencePointEquivCellPoint slot
        ⟨⟨colors slot ⟨i,c⟩,
            Fintype.equivFin
              (fiber (cells slot) (colors slot) (colors slot ⟨i,c⟩))
              ⟨⟨i,c⟩,rfl⟩⟩,x⟩) = _
  rw [hpoint]
  rfl

/-- The fusion-natural chart on the canonical profile occurrence belonging
to a literal cell is exactly the supplied assembly of that slot cell. -/
theorem pointChart_literalCell_apply
    (Block : ι → Type*)
    (slotChart : ∀ i,
      (Σ c : cells slot i, mixturePoints (colors slot ⟨i,c⟩)) ≃ Block i)
    (assemble : (Σ i, Block i) ≃ X)
    (i : ι) (c : (slot i).Cells)
    (x : mixturePoints (colors slot ⟨i,c⟩)) :
    pointChart slot Block slotChart assemble
        ⟨colors slot ⟨i,c⟩, literalOccurrenceIndex slot i c, x⟩ =
      assemble ⟨i,slotChart i ⟨c,x⟩⟩ := by
  change assemble
      ((Equiv.sigmaCongrRight slotChart)
        (literalCellReindex slot
          (indexed_multiplicity (cells slot) (colors slot))
          ⟨colors slot ⟨i,c⟩, literalOccurrenceIndex slot i c, x⟩)) = _
  have h := literalCellReindex_apply slot
    (indexed_multiplicity (cells slot) (colors slot)) i c x
  exact congrArg (fun y ↦ assemble ((Equiv.sigmaCongrRight slotChart) y))
    (by simpa only [literalOccurrenceIndex] using h)

/-- One completed-profile block has exactly the literal assembled range of
its displayed cell.  The left side is in the syntactic form required by the
local full-profile orbit lemma. -/
theorem pointChart_literalCell_range
    (Block : ι → Type*)
    (slotChart : ∀ i,
      (Σ c : cells slot i, mixturePoints (colors slot ⟨i,c⟩)) ≃ Block i)
    (assemble : (Σ i, Block i) ≃ X)
    (i : ι) (c : (slot i).Cells) :
    Set.range (fun x : mixturePoints (colors slot ⟨i,c⟩) ↦
      pointChart slot Block slotChart assemble
        ⟨colors slot ⟨i,c⟩, literalOccurrenceIndex slot i c, x⟩) =
      Set.range (fun x : mixturePoints (colors slot ⟨i,c⟩) ↦
        assemble ⟨i,slotChart i ⟨c,x⟩⟩) := by
  exact congrArg Set.range (funext fun x ↦
    pointChart_literalCell_apply slot Block slotChart assemble i c x)

end SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalCellRange

end
