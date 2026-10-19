import SymmetricSubgroupAsymptotics.Row246OriginalAffineEmbedding
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row246OriginalAffineGeneratorCoordinates
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open Row246OriginalTripleFrame

def offsets : Fin 4 → Fin 4 → ZMod 3 :=
  ![![0,0,0,1],![0,2,0,1],![1,2,1,2],![2,0,1,1]]
def signs : Fin 4 → Fin 4 → ZMod 2 :=
  ![![0,0,0,0],![0,1,0,1],![0,0,0,0],![0,1,0,0]]

private theorem local_apply (a i : Fin 4) (q : Fin 3) :
    (frame.wreathEmbedding (closureGenerators row246Generators a)).left i q =
      (points.symm (row246Generators a
        (points ((tops a)⁻¹ i,q)))).2 := by
  rw [ProductBlockFrame.wreathEmbedding_left_apply]
  have ht := ProductBlockFrame.ofGenerators_top_generator points row246Generators tops
    (by unfold ProductBlockFrame.Preserves; decide +kernel) a
  change frame.top (closureGenerators row246Generators a)=tops a at ht
  rw [ht]
  rfl

theorem offset_generator (a i : Fin 4) :
    (Row246OriginalAffineEmbedding.embedding (closureGenerators row246Generators a)).left.toAdd i =
      offsets a i := by
  change TernaryPermutationWreathEmbedding.offset
    ((frame.wreathEmbedding (closureGenerators row246Generators a)).left i)=offsets a i
  unfold TernaryPermutationWreathEmbedding.offset
  rw [local_apply]
  revert a i
  decide +kernel

theorem sign_generator (a i : Fin 4) :
    (Row246OriginalAffineEmbedding.embedding (closureGenerators row246Generators a)).right.left.toAdd.val i =
      signs a i := by
  change (oddMarkerSign
    ((frame.wreathEmbedding (closureGenerators row246Generators a)).left i)).toAdd=signs a i
  have hp : (frame.wreathEmbedding (closureGenerators row246Generators a)).left i =
      Equiv.ofBijective (fun q : Fin 3 =>
        (points.symm (row246Generators a (points ((tops a)⁻¹ i,q)))).2)
        (by simpa only [← local_apply] using
          ((frame.wreathEmbedding (closureGenerators row246Generators a)).left i).bijective) := by
    apply Equiv.ext
    intro q
    exact local_apply a i q
  rw [hp]
  clear hp
  revert a i
  decide +kernel
end SymmetricSubgroupAsymptotics.Row246OriginalAffineGeneratorCoordinates
