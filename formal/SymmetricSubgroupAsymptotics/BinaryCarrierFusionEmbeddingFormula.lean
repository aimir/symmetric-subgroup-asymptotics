import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalLabelEmbedding
import SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalPointChart
import SymmetricSubgroupAsymptotics.BinaryCarrierFusionNaturalCellRange

/-!
# The literal action behind a fusion-natural carrier chart

The canonical completed-profile enumeration used by a carrier word is only
an intermediate coordinate system.  Once the fusion-natural point chart is
installed, the ambient embedding is the evident action of every retained
carrier on its own displayed cells, followed by the supplied block assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFusionEmbeddingFormula

open SymmetricSubgroupAsymptotics
open BinaryCarrierCellProfile
open BinaryCarrierFusionNaturalPointChart
open BinaryCarrierOriginalLabelEmbedding
open BinaryCarrierParameterProfiles
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  (slot : ι → Slot)

/-- The action of one replacement carrier on its own displayed cells. -/
def displayedCarrierAction (S : Slot) :
    S.carrier →* Equiv.Perm
      (Σ c : S.Cells, mixturePoints (S.color c)) where
  toFun p :=
    { toFun := fun z => ⟨z.1,
        (((p.1 z.1 : mixtureAction (S.color z.1)) : Equiv.Perm _) z.2)⟩
      invFun := fun z => ⟨z.1,
        (((((p.1 z.1)⁻¹ : mixtureAction (S.color z.1))) : Equiv.Perm _)
          z.2)⟩
      left_inv := by rintro ⟨c,x⟩; simp
      right_inv := by rintro ⟨c,x⟩; simp }
  map_one' := by
    apply Equiv.ext
    rintro ⟨c,x⟩
    rfl
  map_mul' p q := by
    apply Equiv.ext
    rintro ⟨c,x⟩
    rfl

@[simp] theorem displayedCarrierAction_apply (S : Slot) (p : S.carrier)
    (z : Σ c : S.Cells, mixturePoints (S.color c)) :
    displayedCarrierAction S p z =
      ⟨z.1, (((p.1 z.1 : mixtureAction (S.color z.1)) : Equiv.Perm _) z.2)⟩ :=
  rfl

/-- The literal sigma of all displayed points, before the blocks are
assembled onto the original ambient labels. -/
abbrev LiteralPoints :=
  Σ i, Σ c : cells slot i, mixturePoints (colors slot ⟨i,c⟩)

/-- The replacement carriers act independently on their literal cells. -/
def literalAction :
    (∀ i, carriers slot i) →* Equiv.Perm (LiteralPoints slot) where
  toFun p :=
    { toFun := fun z => ⟨z.1, z.2.1,
        (((p z.1).1 z.2.1 : mixtureAction (colors slot ⟨z.1,z.2.1⟩)) :
          Equiv.Perm _) z.2.2⟩
      invFun := fun z => ⟨z.1, z.2.1,
        (((((p z.1).1 z.2.1)⁻¹ :
          mixtureAction (colors slot ⟨z.1,z.2.1⟩))) : Equiv.Perm _) z.2.2⟩
      left_inv := by rintro ⟨i,c,x⟩; simp
      right_inv := by rintro ⟨i,c,x⟩; simp }
  map_one' := by
    apply Equiv.ext
    rintro ⟨i,c,x⟩
    rfl
  map_mul' p q := by
    apply Equiv.ext
    rintro ⟨i,c,x⟩
    rfl

@[simp] theorem literalAction_apply (p : ∀ i, carriers slot i)
    (z : LiteralPoints slot) :
    literalAction slot p z =
      ⟨z.1, displayedCarrierAction (slot z.1) (p z.1) z.2⟩ := rfl

/-- Conjugation of permutation groups respects a commuting square of point
equivalences. -/
theorem permCongrHom_comp_of_trans_eq
    {A B P Q : Type*} (left : A ≃ P) (right : B ≃ Q)
    (middle : A ≃ B) (ambient : P ≃ Q)
    (h : left.trans ambient = middle.trans right) :
    ambient.permCongrHom.toMonoidHom.comp
        left.permCongrHom.toMonoidHom =
      right.permCongrHom.toMonoidHom.comp
        middle.permCongrHom.toMonoidHom := by
  change (left.permCongrHom.trans ambient.permCongrHom).toMonoidHom =
    (middle.permCongrHom.trans right.permCongrHom).toMonoidHom
  rw [Equiv.permCongrHom_trans, Equiv.permCongrHom_trans, h]

/-- The last two stages of a fusion-natural point chart: local displayed
points enter their source blocks, and the blocks enter the ambient set. -/
def literalPointChart
    (Block : ι → Type*)
    (slotChart : ∀ i,
      (Σ c : cells slot i, mixturePoints (colors slot ⟨i,c⟩)) ≃ Block i)
    (assemble : (Σ i, Block i) ≃ X) : LiteralPoints slot ≃ X :=
  (Equiv.sigmaCongrRight slotChart).trans assemble

/-- The canonical profile occurrence assigned to a literal cell reads the
same carrier coordinate. -/
theorem originalColorDisplay_apply_literalCell
    (p : ∀ i, carriers slot i) (i : ι) (c : cells slot i) :
    (originalColorDisplay (cells slot) (colors slot)).productEquiv
        (carrierReplacementEmbedding (carriers slot) p)
        (colors slot ⟨i,c⟩)
      (BinaryCarrierFusionNaturalCellRange.literalOccurrenceIndex slot i c) =
      (p i).1 c := by
  have h := assignedProductEquiv_apply mixtureAction
    (profileMultiplicity
      (criticalRank (cells slot) (colors slot))
      (cyclicMultiplicity (cells slot) (colors slot))
      (carrierScale (cells slot) (colors slot))
      (index (cells slot) (colors slot)))
    (cellToProfileOccurrence (cells slot) (colors slot))
    (carrierReplacementEmbedding (carriers slot) p) ⟨i,c⟩
  simpa [BinaryCarrierFusionNaturalCellRange.literalOccurrenceIndex,
    originalColorDisplay, display, assignedProfileDisplay,
    cellToProfileOccurrence,
    cellToOccurrence, occurrenceToCell, Equiv.sigmaCongrRight] using h

/-- After the fusion-natural chart is installed, the abstract ambient
embedding is exactly the literal carrier action on the assembled blocks. -/
theorem ambientEmbedding_pointChart
    (Block : ι → Type*)
    (slotChart : ∀ i,
      (Σ c : cells slot i, mixturePoints (colors slot ⟨i,c⟩)) ≃ Block i)
    (assemble : (Σ i, Block i) ≃ X) :
    ambientEmbedding slot (pointChart slot Block slotChart assemble) =
      (literalPointChart slot Block slotChart assemble).permCongrHom.toMonoidHom.comp
        (literalAction slot) := by
  apply MonoidHom.ext
  intro p
  apply Equiv.ext
  intro z
  obtain ⟨z,rfl⟩ :=
    (literalPointChart slot Block slotChart assemble).surjective z
  rcases z with ⟨i,c,x⟩
  let w : OrbitProfilePoints mixturePoints
      (profileMultiplicity
        (criticalRank (cells slot) (colors slot))
        (cyclicMultiplicity (cells slot) (colors slot))
        (carrierScale (cells slot) (colors slot))
        (index (cells slot) (colors slot))) :=
    ⟨colors slot ⟨i,c⟩,
    BinaryCarrierFusionNaturalCellRange.literalOccurrenceIndex slot i c,x⟩
  have hw : pointChart slot Block slotChart assemble w =
      literalPointChart slot Block slotChart assemble ⟨i,⟨c,x⟩⟩ := by
    exact BinaryCarrierFusionNaturalCellRange.pointChart_literalCell_apply
      slot Block slotChart assemble i c x
  change (pointChart slot Block slotChart assemble).permCongr
      ((orbitProfileProductAction
        (profileMultiplicity
          (criticalRank (cells slot) (colors slot))
          (cyclicMultiplicity (cells slot) (colors slot))
          (carrierScale (cells slot) (colors slot))
          (index (cells slot) (colors slot))) mixtureAction)
        ((originalColorDisplay (cells slot) (colors slot)).productEquiv
          (carrierReplacementEmbedding (carriers slot) p)))
        (literalPointChart slot Block slotChart assemble ⟨i,⟨c,x⟩⟩) =
    (literalPointChart slot Block slotChart assemble).permCongr
      (literalAction slot p)
        (literalPointChart slot Block slotChart assemble ⟨i,⟨c,x⟩⟩)
  rw [Equiv.permCongr_apply, Equiv.permCongr_apply,
    Equiv.symm_apply_apply]
  have hinv : (pointChart slot Block slotChart assemble).symm
      (literalPointChart slot Block slotChart assemble ⟨i,⟨c,x⟩⟩) = w := by
    rw [← hw, Equiv.symm_apply_apply]
  rw [hinv]
  change pointChart slot Block slotChart assemble
      ⟨colors slot ⟨i,c⟩,
        BinaryCarrierFusionNaturalCellRange.literalOccurrenceIndex slot i c,
        (((originalColorDisplay (cells slot) (colors slot)).productEquiv
            (carrierReplacementEmbedding (carriers slot) p)
            (colors slot ⟨i,c⟩)
            (BinaryCarrierFusionNaturalCellRange.literalOccurrenceIndex
              slot i c) : mixtureAction _) : Equiv.Perm _) x⟩ = _
  rw [originalColorDisplay_apply_literalCell]
  exact BinaryCarrierFusionNaturalCellRange.pointChart_literalCell_apply
    slot Block slotChart assemble i c _

/-- The same formula after an arbitrary final change of ambient labels. -/
theorem ambientEmbedding_pointChart_trans
    {Y : Type*}
    (Block : ι → Type*)
    (slotChart : ∀ i,
      (Σ c : cells slot i, mixturePoints (colors slot ⟨i,c⟩)) ≃ Block i)
    (assemble : (Σ i, Block i) ≃ X) (f : X ≃ Y) :
    ambientEmbedding slot
        ((pointChart slot Block slotChart assemble).trans f) =
      ((literalPointChart slot Block slotChart assemble).trans f).permCongrHom.toMonoidHom.comp
        (literalAction slot) := by
  have hp : pointChart slot Block slotChart (assemble.trans f) =
      (pointChart slot Block slotChart assemble).trans f := by
    apply Equiv.ext
    intro z
    rfl
  have hl : literalPointChart slot Block slotChart (assemble.trans f) =
      (literalPointChart slot Block slotChart assemble).trans f := by
    apply Equiv.ext
    intro z
    rfl
  rw [← hp, ← hl]
  exact ambientEmbedding_pointChart slot Block slotChart (assemble.trans f)

end SymmetricSubgroupAsymptotics.BinaryCarrierFusionEmbeddingFormula

end
