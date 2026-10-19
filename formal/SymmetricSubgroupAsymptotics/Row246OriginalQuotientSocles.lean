import SymmetricSubgroupAsymptotics.Row246ActualSignedImage
import SymmetricSubgroupAsymptotics.ActualBinaryFourMonomialQuotientSocles
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row246OriginalQuotientSocles
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open Row246OriginalAffineEmbedding
open KleinParitySignedBinaryTop (E)

 theorem actual_quotient (N : Subgroup image) [N.Normal] :
    SocleNormalGeneratorBound (image ⧸ N) 2 :=
  ActualBinaryFourMonomialQuotientSocles.quotientSocle
    (TernarySignedPermutationSubgroupSocles.blockPermutation E)
    (TernarySignedPermutationSubgroupSocles.coefficient E)
    (TernarySignedPermutationSubgroupSocles.coefficient_one E)
    (TernarySignedPermutationSubgroupSocles.coefficient_mul E)
    image Row246ActualSignedImage.isPGroup
    (fun L => by letI := L.property; exact Row246ActualSignedImage.relative_heads L.val)
    Row246ActualSignedImage.transitive N

 theorem quotientSocle (N : Subgroup row246Interface.top) [N.Normal] :
    SocleNormalGeneratorBound (row246Interface.top ⧸ N) 2 := by
  let f : image →* row246Interface.top ⧸ N :=
    (QuotientGroup.mk' N).comp originalEquiv.symm.toMonoidHom
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective N).comp originalEquiv.symm.surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective f hf) (actual_quotient f.ker)
end SymmetricSubgroupAsymptotics.Row246OriginalQuotientSocles
