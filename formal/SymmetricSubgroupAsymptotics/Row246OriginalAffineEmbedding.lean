import SymmetricSubgroupAsymptotics.Row246OriginalTripleFrame
import SymmetricSubgroupAsymptotics.TernaryPermutationWreathEmbedding

/-! Literal affine image of the original row246 subgroup. No translation
surjectivity or splitting assumption is imposed on this actual image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row246OriginalAffineEmbedding
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open FourBlockKleinSignBase (Base)

abbrev Target := TernaryPermutationWreathEmbedding.Target (R := Base) (I := Fin 4)

def embedding : row246Interface.top →* Target :=
  TernaryPermutationWreathEmbedding.affine.comp Row246OriginalTripleFrame.wreathEmbedding

theorem embedding_injective : Function.Injective embedding :=
  TernaryPermutationWreathEmbedding.affine_injective.comp
    Row246OriginalTripleFrame.wreathEmbedding_injective

def image : Subgroup Target := embedding.range

def originalEquiv : row246Interface.top ≃* image :=
  MulEquiv.ofBijective embedding.rangeRestrict
    ⟨fun _ _ h => embedding_injective (congrArg Subtype.val h),
      embedding.rangeRestrict_surjective⟩

@[simp] theorem originalEquiv_val (u : row246Interface.top) :
    (originalEquiv u).val = embedding u := rfl

@[simp] theorem embedding_block (u : row246Interface.top) :
    (embedding u).right.right = Row246OriginalTripleFrame.top u := rfl

end SymmetricSubgroupAsymptotics.Row246OriginalAffineEmbedding
