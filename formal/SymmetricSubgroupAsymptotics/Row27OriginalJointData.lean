import SymmetricSubgroupAsymptotics.Row27OriginalKernelProfile
import SymmetricSubgroupAsymptotics.Row27OriginalAbelianAxes
import SymmetricSubgroupAsymptotics.BinarySymmetricThreeUniformTwoOriginalSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlipNormNaturalFamily
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row27OriginalJointData
open Row27OriginalQuartetFrame Row27OriginalKernelProfile
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
local instance : Finite ActualR := by
  change Finite (Additive frame.top.ker)
  infer_instance
local instance : FiniteDimensional (ZMod 2) ActualR := Module.Finite.of_finite
 theorem quotientSocle (N : Subgroup Row27Top) [N.Normal] :
    SocleNormalGeneratorBound (Row27Top ⧸ N) 2 :=
  BinarySymmetricThreeUniformTwoOriginalSocles.quotientSocle (X:=Fin 12) (by simp)
    frame.top top_surjective ActualR actualChart uniform_two
    Row27OriginalAbelianAxes.cover Row27OriginalAbelianAxes.cover_surjective N
 def jointData : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData row27Interface 2 2 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds _ (fun N => by
    letI := N.2
    exact quotientSocle N.1)
  natural := PrimitiveAffineDegreeTwoTwelveFlipNormNaturalFamily.row27NaturalTwo
 def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row27Interface :=
  .ofExact jointData (by decide +kernel)
end SymmetricSubgroupAsymptotics.Row27OriginalJointData
