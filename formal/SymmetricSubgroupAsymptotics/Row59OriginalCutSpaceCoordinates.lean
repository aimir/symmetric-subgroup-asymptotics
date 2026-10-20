import SymmetricSubgroupAsymptotics.Row59OriginalCutSpaceFrame
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row59OriginalCutSpaceCoordinates
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open Row59OriginalCutSpaceFrame

theorem top_bind (u : row59Interface.top) :
    SymmetricFourTwelvePointSocles.edge (top u).val=frame.top u := by
  have h := congrArg Subtype.val (topEquiv.apply_symm_apply (frame.top.rangeRestrict u))
  change SymmetricFourTwelvePointSocles.edge (top u).val=frame.top u at h
  exact h

theorem top_generator (i : Fin 4) : top (original i)=codes i := by
  apply Subtype.ext
  have hi : Function.Injective SymmetricFourTwelvePointSocles.edge := by decide +kernel
  apply hi
  have h := BinaryPairFrame.ofGenerators_top_generator points row59Generators tops
    (by unfold BinaryPairFrame.Preserves; decide +kernel) i
  exact (top_bind (original i)).trans h

theorem coordinate_apply (k : top.ker) (i : Fin 6) :
    inclusion (originalKernelChart.equiv.symm k).toAdd i=
      (points.symm ((k.val : Equiv.Perm (Fin 12)) (points (i,0)))).2 := rfl
end SymmetricSubgroupAsymptotics.Row59OriginalCutSpaceCoordinates
