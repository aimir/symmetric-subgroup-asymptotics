import SymmetricSubgroupAsymptotics.Non2PreE7ActualBlockCompression
import SymmetricSubgroupAsymptotics.SemisimpleCompressionRoundingGap

/-! Actual block-wreath compression under a positive local parity gap.
The literal semisimple kernel and quotient embedding are unchanged; a
bounded local degree pays the same fixed global padding margin. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

structure PreE7AbstractBlockWreathRoundingData
    (w : ℕ) (i : PreE7NonPairActionClass w)
    (D Q I : Type) [Group D] [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I] where
  width_lower : 5 ≤ w
  blockSize : ℕ
  localDegree : ℕ
  localDegree_pos : 0 < localDegree
  width_eq : w = blockSize * Fintype.card I
  localQuotient : Subgroup (Equiv.Perm (Fin localDegree))
  localMap : D →* localQuotient
  localChart : SemisimpleNormalChart localMap.ker
  ambientEmbedding :
    preE7NonPairAction w i →* PermutationalWreathProduct D Q I
  ambientEmbedding_injective : Function.Injective ambientEmbedding
  fullComponent :
    PermutationalWreathProduct.Compression.FullComponent ambientEmbedding
  blockSize_bound : blockSize≤1024
  localDegree_gap : max 2 localDegree+1≤evenWidth blockSize

namespace PreE7AbstractBlockWreathRoundingData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  {D Q I : Type} [Group D] [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]
  (C : PreE7AbstractBlockWreathRoundingData w i D Q I)

abbrev E : Subgroup (preE7NonPairAction w i) :=
  PermutationalWreathProduct.Compression.kernel
    C.ambientEmbedding C.localMap

def quotientDegree : ℕ := C.localDegree * Fintype.card I

def quotientEmbedding :
    (preE7NonPairAction w i ⧸ C.E) →*
      PermutationalWreathProduct C.localQuotient Q I :=
  PermutationalWreathProduct.Compression.quotientEmbedding
    C.ambientEmbedding C.localMap

/-- The faithful compressed action retains the literal top point set until
the final finite relabeling. -/
def quotientAction :
    (preE7NonPairAction w i ⧸ C.E) →*
      Equiv.Perm (Fin C.quotientDegree) := by
  letI : Nonempty (Fin C.localDegree) :=
    Fin.pos_iff_nonempty.mp C.localDegree_pos
  exact
    (PermutationalWreathProduct.toFintypePerm
      (u := C.localDegree) C.localQuotient Q I).comp C.quotientEmbedding

theorem quotientAction_injective : Function.Injective C.quotientAction := by
  letI : Nonempty (Fin C.localDegree) :=
    Fin.pos_iff_nonempty.mp C.localDegree_pos
  exact
    (PermutationalWreathProduct.toFintypePerm_injective
      (u := C.localDegree) C.localQuotient Q I).comp
        (PermutationalWreathProduct.Compression.quotientEmbedding_injective
          C.ambientEmbedding C.localMap)

/-- Arbitrary literal block sets therefore supply the complete semisimple
compression interface. -/
noncomputable def toSemisimpleMarginData :
    PreE7SemisimpleMarginData w i where
  width_lower := C.width_lower
  E := C.E
  E_normal := inferInstance
  chart :=
    PermutationalWreathProduct.Compression.kernelSemisimpleChartOfFullComponent
      C.ambientEmbedding C.localMap C.ambientEmbedding_injective
      C.fullComponent C.localChart
  quotientDegree := C.quotientDegree
  quotientAction := C.quotientAction
  quotientAction_injective := C.quotientAction_injective
  quotientDegree_margin := by
    have h := PreE7SemisimpleMarginData.margin_of_local_rounding_gap
      C.blockSize_bound
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)) C.localDegree_gap
    simpa only [C.width_eq,quotientDegree,Nat.cast_mul] using h

end PreE7AbstractBlockWreathRoundingData

/-- The genuinely local certificate left by a selected original minimal
block.  The global kernel, semisimple chart, quotient embedding and faithful
quotient action will all be constructed from it. -/
structure PreE7OriginalMinimalBlockRoundingData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 5 ≤ w
  basePoint : Fin w
  block : OriginalMinimalBlock
    (A := preE7NonPairAction w i) basePoint
  localDegree : ℕ
  localDegree_pos : 0 < localDegree
  localQuotient : Subgroup (Equiv.Perm (Fin localDegree))
  localMap : block.Component →* localQuotient
  localChart : SemisimpleNormalChart localMap.ker
  blockSize_bound : Nat.card block.Fibre≤1024
  localDegree_gap : max 2 localDegree+1≤evenWidth (Nat.card block.Fibre)

namespace PreE7OriginalMinimalBlockRoundingData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7OriginalMinimalBlockRoundingData w i)

/-- The standard actual block embedding fills every global field of the
abstract wreath certificate. -/
noncomputable def toAbstractBlockWreathData :
    PreE7AbstractBlockWreathRoundingData w i C.block.Component C.block.Top
      C.block.Points where
  width_lower := C.width_lower
  blockSize := Nat.card C.block.Fibre
  localDegree := C.localDegree
  localDegree_pos := C.localDegree_pos
  width_eq := by
    simpa using C.block.degree_product.symm
  localQuotient := C.localQuotient
  localMap := C.localMap
  localChart := C.localChart
  ambientEmbedding :=
    ActualBlockWreathEmbedding.embedding C.block.map
      C.block.map_equivariant C.block.base
  ambientEmbedding_injective :=
    ActualBlockWreathEmbedding.embedding_injective C.block.map
      C.block.map_equivariant C.block.base
  fullComponent :=
    ActualBlockWreathEmbedding.fullComponent C.block.map
      C.block.map_equivariant C.block.base
  blockSize_bound := C.blockSize_bound
  localDegree_gap := C.localDegree_gap

/-- A local primitive-component compression certificate on an actual
minimal block enters the complete semisimple COMP source directly. -/
noncomputable def toSemisimpleMarginData :
    PreE7SemisimpleMarginData w i :=
  C.toAbstractBlockWreathData.toSemisimpleMarginData

end PreE7OriginalMinimalBlockRoundingData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
