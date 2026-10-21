import SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData
import SymmetricSubgroupAsymptotics.PrimitiveTwelveActualQuotientSocleThree

/-! The two actual primitive-twelve tops use the existing admissible
(3,1) profile. Both normal axes and the original natural-module
certificates are unchanged; no quotient order-two claim is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData.DirectConsumers
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem row179_quotientSocle
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) (N : Subgroup Row179Top) [N.Normal] :
    SocleNormalGeneratorBound (Row179Top ⧸ N) 3 :=
  PrimitiveSocleRawStructure.primitive_degreeTwelve_quotientSocle_three hindex N

theorem row218_quotientSocle
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) (N : Subgroup Row218Top) [N.Normal] :
    SocleNormalGeneratorBound (Row218Top ⧸ N) 3 :=
  PrimitiveSocleRawStructure.primitive_degreeTwelve_quotientSocle_three hindex N

def row179Family (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) : row179Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row179Interface.normalRegistry (fun N => by
      letI := N.2
      exact row179_quotientSocle hindex N.1)

def row218Family (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) : row218Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row218Interface.normalRegistry (fun N => by
      letI := N.2
      exact row218_quotientSocle hindex N.1)

def row179Data (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData
    row179Interface 3 1 where
  topSocle := row179Family hindex
  natural := PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily.row179Natural

def row218Data (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) : DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData
    row218Interface 3 1 where
  topSocle := row218Family hindex
  natural := PrimitiveAffineDegreeTwoTwelveElevenCycleNaturalFamily.row218Natural

def row179Flexible (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) : DegreeTwoTwelveFlexibleProfiles.Data row179Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (row179Data hindex) (by decide +kernel)

def row218Flexible (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) : DegreeTwoTwelveFlexibleProfiles.Data row218Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact (row218Data hindex) (by decide +kernel)

end SymmetricSubgroupAsymptotics.Row179SharedOriginalJointData.DirectConsumers
