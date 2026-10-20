import SymmetricSubgroupAsymptotics.Row62OriginalKernelCertificate
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row62OriginalKernelProfile
open Row62OriginalQuartetFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open CyclicFourAugmentationTranslations (Model)
private def rangeMap : frame.top.ker →* Row62CyclicFourKernelModel.action.range :=
  (Row62Top.subtype.comp frame.top.ker.subtype).codRestrict _
    Row62OriginalKernelCertificate.kernel_mem
private def modelEquiv : Model ≃* Row62CyclicFourKernelModel.action.range :=
  MonoidHom.ofInjective Row62CyclicFourKernelModel.action_injective
 def embedding : frame.top.ker →* Model := modelEquiv.symm.toMonoidHom.comp rangeMap
 theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg modelEquiv h
  have hv := congrArg (fun z : Row62CyclicFourKernelModel.action.range => z.val) he
  simpa [embedding,rangeMap] using hv
 theorem binary_group : IsPGroup 2 frame.top.ker :=
  CyclicFourAugmentationTranslations.binary_group.of_injective embedding embedding_injective
 theorem commutative : IsMulCommutative frame.top.ker := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply embedding_injective
  simp only [map_mul,mul_comm]
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
 theorem relative_rank (L : Subgroup Row62Top) [L.Normal] (hL : L≤frame.top.ker) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤2 := by
  let inc : L →* frame.top.ker := Subgroup.inclusion hL
  have hi : Function.Injective inc := Subgroup.inclusion_injective hL
  exact (Submodule.finrank_le (primeRelativeCharacters 2 L)).trans
    (primeCharacterRank_le_of_injective 2 CyclicFourAugmentationTranslations.binary_rank
      (embedding.comp inc) (embedding_injective.comp hi))
end SymmetricSubgroupAsymptotics.Row62OriginalKernelProfile
