import SymmetricSubgroupAsymptotics.SixPairAbelianKernelLocalDichotomy
import SymmetricSubgroupAsymptotics.SixPairElementaryCoarseKernelSource
import SymmetricSubgroupAsymptotics.SixPairC4KernelThreeSource

/-! Complete source for EVERY actual abelian three-pair coarse kernel.
The original action gives either literal C4³ coordinates or the elementary
branch. Both branches prove their all-original-normal counts internally. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairAbelianCoarseKernelSource
open Non2UnipotentPrefixFiniteMenu

 def source (p : PreE7PairActionClass 6)
    [MulAction.IsPretransitive (preE7PairAction 6 p) (Fin 12)]
    (F : BinaryPairFrame (preE7PairAction 6 p) (Fin 6))
    (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))
    (hcomm : ∀ a b : (SixPairNestedTopFrames.nestedFrame F E).top.ker,a*b=b*a)
    (hKP : KovacsPraegerAbelianizationBound) (hM4 : GlobalMarkedC4MomentBound) :
    PreE7RankTailSourceOrYonedaTopData 12 (preE7SixPairNonPairAction p) := by
  classical
  let h := SixPairAbelianKernelLocalDichotomy.coordinates_or_square_one F E hcomm
  by_cases h4 : ∃ j : (SixPairNestedTopFrames.nestedFrame F E).top.ker →*
      (Fin 3 → C4CoordinateHomCount.C4),Function.Injective j
  · exact SixPairC4KernelThreeSource.source p F E (Classical.choose h4)
      (Classical.choose_spec h4) hKP hM4
  · exact SixPairElementaryCoarseKernelSource.source p F E (h.resolve_left h4) hKP

end SymmetricSubgroupAsymptotics.SixPairAbelianCoarseKernelSource
