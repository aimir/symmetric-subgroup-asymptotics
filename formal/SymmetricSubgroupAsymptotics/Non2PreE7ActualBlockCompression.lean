import SymmetricSubgroupAsymptotics.ActualBlockWreathEmbedding
import SymmetricSubgroupAsymptotics.Non2PreE7ExactBlockCompression
import SymmetricSubgroupAsymptotics.OriginalMinimalBlock
import SymmetricSubgroupAsymptotics.PermutationalWreathProduct

/-!
# Actual block systems enter semisimple compression

This file removes the last global input from exact block compression.  An
arbitrary finite literal block set may be retained in the wreath product;
its product action is relabelled only at the final faithful permutation
representation.  For an `OriginalMinimalBlock`, the standard wreath
embedding and exact-component fullness are constructed automatically.

Thus the only structural datum still supplied by a primitive block analysis
is local: a quotient of the literal block component with semisimple kernel
and sufficiently small faithful degree.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

instance preE7NonPairAction_pretransitive (w : ℕ)
    (i : PreE7NonPairActionClass w) :
    MulAction.IsPretransitive (preE7NonPairAction w i) (Fin w) :=
  Non2TransitiveActionClass.representative_pretransitive i.1.1

/-- Construction-facing exact block data over an arbitrary literal finite
block set.  This form is what the standard block-system wreath embedding
actually produces. -/
structure PreE7AbstractBlockWreathData
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
  localDegree_small : 2 * localDegree ≤ evenWidth blockSize

namespace PreE7AbstractBlockWreathData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  {D Q I : Type} [Group D] [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]
  (C : PreE7AbstractBlockWreathData w i D Q I)

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

theorem quotientDegree_small :
    2 * C.quotientDegree ≤ evenWidth w := by
  unfold quotientDegree
  calc
    2 * (C.localDegree * Fintype.card I) ≤
        evenWidth (C.blockSize * Fintype.card I) :=
      evenWidth_mul_block_bound C.localDegree_small
    _ = evenWidth w := congrArg evenWidth C.width_eq.symm

/-- Arbitrary literal block sets therefore supply the complete semisimple
compression interface. -/
noncomputable def toSemisimpleCompressionData :
    PreE7SemisimpleCompressionData w i where
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
  quotientDegree_small := C.quotientDegree_small

end PreE7AbstractBlockWreathData

/-- The genuinely local certificate left by a selected original minimal
block.  The global kernel, semisimple chart, quotient embedding and faithful
quotient action will all be constructed from it. -/
structure PreE7OriginalMinimalBlockCompressionData
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
  localDegree_small :
    2 * localDegree ≤ evenWidth (Nat.card block.Fibre)

namespace PreE7OriginalMinimalBlockCompressionData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7OriginalMinimalBlockCompressionData w i)

/-- The standard actual block embedding fills every global field of the
abstract wreath certificate. -/
noncomputable def toAbstractBlockWreathData :
    PreE7AbstractBlockWreathData w i C.block.Component C.block.Top
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
  localDegree_small := C.localDegree_small

/-- A local primitive-component compression certificate on an actual
minimal block enters the complete semisimple COMP source directly. -/
noncomputable def toSemisimpleCompressionData :
    PreE7SemisimpleCompressionData w i :=
  C.toAbstractBlockWreathData.toSemisimpleCompressionData

end PreE7OriginalMinimalBlockCompressionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
