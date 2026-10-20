import SymmetricSubgroupAsymptotics.SixPairFullIndependentSource
import SymmetricSubgroupAsymptotics.SixPairFullKernelIndependenceOfOrder

/-! The complete representative-facing source follows from the actual
maximal coarse-kernel order. A catalogue integer without an actual
original kernel-cardinality proof does not instantiate this theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelOrderSource
open Non2UnipotentPrefixFiniteMenu

def source (p : PreE7PairActionClass 6)
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)]
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
    (hcard : Nat.card (SixPairNestedTopFrames.nestedFrame F E).top.ker=512)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) :=
  SixPairFullIndependentSource.source p F E
    (SixPairFullKernelIndependenceOfOrder.independent F E hcard) hZmud lit

end SymmetricSubgroupAsymptotics.SixPairFullKernelOrderSource
