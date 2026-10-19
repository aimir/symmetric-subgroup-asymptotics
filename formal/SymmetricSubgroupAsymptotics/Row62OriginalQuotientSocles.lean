import SymmetricSubgroupAsymptotics.Row62OriginalKernelProfile
import SymmetricSubgroupAsymptotics.Row62OriginalAbelianAxes
import SymmetricSubgroupAsymptotics.NaturalThreeProperBinaryRelativeHead
import SymmetricSubgroupAsymptotics.BinaryKernelZeroProperTopRelativeHeads
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralOriginalQuotientSocles
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row62OriginalQuotientSocles
open Row62OriginalQuartetFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
theorem relative_head (M : Subgroup Row62Top) [M.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M)≤2 :=
  BinaryKernelZeroProperTopRelativeHeads.relative_head_le_two
    NaturalThreeProperBinaryRelativeHead.relative_head_zero frame.top top_surjective
    Row62OriginalKernelProfile.commutative Row62OriginalKernelProfile.relative_rank
    Row62OriginalAbelianAxes.cover Row62OriginalAbelianAxes.cover_surjective M
 theorem quotientSocle (N : Subgroup Row62Top) [N.Normal] :
    SocleNormalGeneratorBound (Row62Top ⧸ N) 2 :=
  TwelvePointRemainingStructural.quotientSocle_two_of_original_symmetricThree
    (X:=Fin 12) (by simp) frame.top top_surjective
    Row62OriginalKernelProfile.binary_group relative_head N
end SymmetricSubgroupAsymptotics.Row62OriginalQuotientSocles
