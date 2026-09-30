import SymmetricSubgroupAsymptotics.BinaryCarrierActualDecoratedProducer

/-!
# Fusion-natural point charts for heterogeneous carrier words

The ordinary carrier producer places the displayed word on a canonical
`Fin` labelling.  For incidence reconstruction we instead assemble the
displayed cells back onto the literal blocks from which they came.  This
file performs the generic dependent reindexing once: a point chart for every
slot, followed by a chart assembling the literal blocks, gives a point chart
for the completed mixture profile selected by the word.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalPointChart

open SymmetricSubgroupAsymptotics
open BinaryCarrierActualDecoratedProducer
open BinaryCarrierCellProfile
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure

/-- Separate the colour/occurrence pair from the local point in an orbit
profile point. -/
def profilePointEquivOccurrencePoint
    {γ : Type*} (Ω : γ → Type*) (m : γ → ℕ) :
    OrbitProfilePoints Ω m ≃ (Σ o : (Σ g, Fin (m g)), Ω o.1) where
  toFun z := ⟨⟨z.1,z.2.1⟩,z.2.2⟩
  invFun z := ⟨z.1.1,(z.1.2,z.2)⟩
  left_inv := fun ⟨g,j,x⟩ ↦ rfl
  right_inv := fun ⟨⟨g,j⟩,x⟩ ↦ rfl

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  (slot : ι → Slot)

/-- Reindex target-profile occurrence points by the literal word cells.
The only type transport is the equality saying that the canonical occurrence
enumeration preserves the cell colour. -/
def occurrencePointEquivCellPoint :
    (Σ o : (Σ g, Fin (multiplicity (cells slot) (colors slot) g)),
        mixturePoints o.1) ≃
      (Σ c : (Σ i, cells slot i), mixturePoints (colors slot c)) :=
  Equiv.sigmaCongr
    (occurrenceToCell (cells slot) (colors slot))
    (fun o ↦ Equiv.cast (congrArg mixturePoints
      (occurrenceToCell_color (cells slot) (colors slot) o).symm))

/-- Assemble the completed target profile on a supplied family of literal
blocks.  A slot chart may keep a proper nonabelian subdirect carrier intact;
only its displayed point set is identified with the block it occupies. -/
def pointChart
    (Block : ι → Type*)
    (slotChart : ∀ i,
      (Σ c : cells slot i, mixturePoints (colors slot ⟨i,c⟩)) ≃ Block i)
    (assemble : (Σ i, Block i) ≃ X) :
    OrbitProfilePoints mixturePoints
      (profileMultiplicity
        (criticalRank (cells slot) (colors slot))
        (cyclicMultiplicity (cells slot) (colors slot))
        (carrierScale (cells slot) (colors slot))
        (index (cells slot) (colors slot))) ≃ X :=
  (Equiv.cast (congrArg (OrbitProfilePoints mixturePoints)
      (indexed_multiplicity (cells slot) (colors slot)))).trans
    ((profilePointEquivOccurrencePoint mixturePoints
      (multiplicity (cells slot) (colors slot))).trans
    ((occurrencePointEquivCellPoint slot).trans
    ((Equiv.sigmaAssoc (fun i c ↦
        mixturePoints (colors slot ⟨i,c⟩))).trans
    ((Equiv.sigmaCongrRight slotChart).trans assemble))))

end SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalPointChart

end
