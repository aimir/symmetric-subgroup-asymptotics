import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.ProductBlockFrameGenerators

/-! Retain the actual minimal block quotient and its physical fibres while
choosing finite coordinate types. No quotient or component is replaced by an
unrelated group with the same order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {X : Type} {P : Subgroup (Equiv.Perm X)}
  [MulAction.IsPretransitive P X] {x0 : X}
  (D : OriginalMinimalBlock (A := P) x0)
  {I F : Type} (eI : D.Points ≃ I) (eF : D.Fibre ≃ F)

private def physicalCoordinates : I × F ≃ X :=
  ((Equiv.prodCongr eI.symm eF.symm).trans (Equiv.prodComm _ _)).trans
    (ActualBlockWreathEmbedding.productEquiv D.map D.map_equivariant D.base)

private theorem physicalCoordinates_block (x : X) :
    eI (D.map x) = ((physicalCoordinates D eI eF).symm x).1 := rfl

/-- The actual top homomorphism, transported only by the chosen point chart. -/
def productFrame : ProductBlockFrame P I F where
  frame := physicalCoordinates D eI eF
  top := eI.permCongrHom.toMonoidHom.comp D.topMap
  intertwine := by
    intro p z
    rw [← physicalCoordinates_block]
    change eI (D.map (p • physicalCoordinates D eI eF z)) =
      eI (p • eI.symm z.1)
    rw [D.map_equivariant]
    change eI (D.topMap p (D.map (physicalCoordinates D eI eF z))) =
      eI (D.topMap p (eI.symm z.1))
    congr 1
    apply congrArg (D.topMap p)
    apply eI.injective
    rw [physicalCoordinates_block D eI eF]
    simpa only [Equiv.apply_symm_apply] using
      congrArg Prod.fst ((physicalCoordinates D eI eF).symm_apply_apply z)

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
