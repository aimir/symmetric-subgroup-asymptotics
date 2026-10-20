import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer
import SymmetricSubgroupAsymptotics.BinaryFourLocalCubicPointGauge

/-! Actual physical fibres, labelled by the same transporters as the
original wreath embedding. Their four-point charts are constructed from
the original fibre cardinality, not supplied as numerical certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)

def originalPhysicalFibreEquiv (i : block.Points) :
    block.Fibre ≃ originalBlockFibre block.map i where
  toFun x := ⟨ActualBlockWreathEmbedding.representative block.base i • x.1, by
    rw [block.map_equivariant,x.2,ActualBlockWreathEmbedding.representative_smul]⟩
  invFun x := ⟨(ActualBlockWreathEmbedding.representative block.base i)⁻¹ • x.1, by
    rw [block.map_equivariant,x.2,ActualBlockWreathEmbedding.representative_inv_smul]⟩
  left_inv x := Subtype.ext (inv_smul_smul _ _)
  right_inv x := Subtype.ext (smul_inv_smul _ _)

def originalLabelledFibreEquiv (d : block.Points ≃ Fin 4) (j : Fin 4) :
    block.Fibre ≃ {x : Fin w // d (block.map x) = j} :=
  (originalPhysicalFibreEquiv block (d.symm j)).trans
    (Equiv.subtypeEquivRight (fun x => by
      constructor
      · intro h
        rw [h,d.apply_symm_apply]
      · intro h
        apply d.injective
        exact h.trans (d.apply_symm_apply j).symm))

def originalRawLabelledFibreChart (hr : Nat.card block.Fibre = 4)
    (d : block.Points ≃ Fin 4) (j : Fin 4) :
    BinaryFourBlockAugmentation.Local ≃ {x : Fin w // d (block.map x) = j} :=
  BinaryFourLocalCubicPointGauge.pointEquiv.symm.trans
    ((Finite.equivFinOfCardEq hr).symm.trans (originalLabelledFibreEquiv block d j))

theorem originalPhysicalFibreEquiv_action
    (i : block.Points) (g : preE7NonPairAction w U) (hi : g • i = i)
    (v : block.Fibre) :
    originalPhysicalFibreEquiv block i
        (((ambientEmbedding block g).left i) • v) =
      (⟨g • (originalPhysicalFibreEquiv block i v).1, by
        rw [block.map_equivariant,(originalPhysicalFibreEquiv block i v).2,hi]⟩ :
          originalBlockFibre block.map i) := by
  apply Subtype.ext
  have hgi : g⁻¹ • i = i := by
    calc
      g⁻¹ • i = g⁻¹ • (g • i) := by rw [hi]
      _ = i := inv_smul_smul g i
  change ActualBlockWreathEmbedding.representative block.base i •
      (((ActualBlockWreathEmbedding.localStabilizer block.base g i :
        preE7NonPairAction w U) • v.1)) =
    g • (ActualBlockWreathEmbedding.representative block.base i • v.1)
  simp only [ActualBlockWreathEmbedding.localStabilizer,hgi,mul_smul,
    smul_inv_smul]

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
