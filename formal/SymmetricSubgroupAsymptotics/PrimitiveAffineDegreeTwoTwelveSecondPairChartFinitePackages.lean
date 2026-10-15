import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartExactSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSecondPairChartPilot
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow94NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses

/-! Seventeen original joint actions in a shared second physical pair chart.
Nine keep their historical capacities; eight use proved alternate (3,1)
profiles from the existing numerical menu. The previously checked natural
bounds concern these same literal actions. No literature input is added. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSecondPairChartFinitePackages

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

/-- Original row51, zero-based index50, joint; historical (2,1). -/
def row51 : DegreeTwoTwelveJointFiniteRowData row51Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartExactSocles.row51_family
  natural := PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily.row51Natural

noncomputable def row51Data : DegreeTwoTwelveFlexibleProfiles.Data row51Interface :=
  .ofExact row51 (by decide +kernel)

/-- Original row52, zero-based index51, joint; historical (2,1). -/
def row52At3 : DegreeTwoTwelveJointFiniteRowData row52Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row52AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily.row52Natural

noncomputable def row52At3Data : DegreeTwoTwelveFlexibleProfiles.Data row52Interface :=
  .ofExact row52At3 (by decide +kernel)

/-- Original row53, zero-based index52, joint; historical (2,1). -/
def row53At3 : DegreeTwoTwelveJointFiniteRowData row53Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row53AtThree_family
  natural := DegreeTwoTwelveSharedNaturalWitnesses.row53Natural

noncomputable def row53At3Data : DegreeTwoTwelveFlexibleProfiles.Data row53Interface :=
  .ofExact row53At3 (by decide +kernel)

/-- Original row86, zero-based index85, joint; historical (3,1). -/
def row86 : DegreeTwoTwelveJointFiniteRowData row86Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row86_family
  natural := PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily.row86Natural

noncomputable def row86Data : DegreeTwoTwelveFlexibleProfiles.Data row86Interface :=
  .ofExact row86 (by decide +kernel)

/-- Original row141, zero-based index140, joint; historical (2,1). -/
def row141 : DegreeTwoTwelveJointFiniteRowData row141Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartExactSocles.row141_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row141Natural

noncomputable def row141Data : DegreeTwoTwelveFlexibleProfiles.Data row141Interface :=
  .ofExact row141 (by decide +kernel)

/-- Original row142, zero-based index141, joint; historical (2,1). -/
def row142 : DegreeTwoTwelveJointFiniteRowData row142Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartExactSocles.row142_family
  natural := PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily.row142Natural

noncomputable def row142Data : DegreeTwoTwelveFlexibleProfiles.Data row142Interface :=
  .ofExact row142 (by decide +kernel)

/-- Original row148, zero-based index147, joint; historical (2,1). -/
def row148At3 : DegreeTwoTwelveJointFiniteRowData row148Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartPilot.row148AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily.row148Natural

noncomputable def row148At3Data : DegreeTwoTwelveFlexibleProfiles.Data row148Interface :=
  .ofExact row148At3 (by decide +kernel)

/-- Original row150, zero-based index149, joint; historical (2,1). -/
def row150At3 : DegreeTwoTwelveJointFiniteRowData row150Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row150AtThree_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row150Natural

noncomputable def row150At3Data : DegreeTwoTwelveFlexibleProfiles.Data row150Interface :=
  .ofExact row150At3 (by decide +kernel)

/-- Original row151, zero-based index150, joint; historical (2,1). -/
def row151At3 : DegreeTwoTwelveJointFiniteRowData row151Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row151AtThree_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row151Natural

noncomputable def row151At3Data : DegreeTwoTwelveFlexibleProfiles.Data row151Interface :=
  .ofExact row151At3 (by decide +kernel)

/-- Original row185, zero-based index184, joint; historical (3,1). -/
def row185 : DegreeTwoTwelveJointFiniteRowData row185Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row185_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row185Natural

noncomputable def row185Data : DegreeTwoTwelveFlexibleProfiles.Data row185Interface :=
  .ofExact row185 (by decide +kernel)

/-- Original row186, zero-based index185, joint; historical (3,1). -/
def row186 : DegreeTwoTwelveJointFiniteRowData row186Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row186_family
  natural := PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily.row186Natural

noncomputable def row186Data : DegreeTwoTwelveFlexibleProfiles.Data row186Interface :=
  .ofExact row186 (by decide +kernel)

/-- Original row189, zero-based index188, joint; historical (2,1). -/
def row189 : DegreeTwoTwelveJointFiniteRowData row189Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartExactSocles.row189_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row189Natural

noncomputable def row189Data : DegreeTwoTwelveFlexibleProfiles.Data row189Interface :=
  .ofExact row189 (by decide +kernel)

/-- Original row221, zero-based index220, joint; historical (2,1). -/
def row221At3 : DegreeTwoTwelveJointFiniteRowData row221Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row221AtThree_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row221Natural

noncomputable def row221At3Data : DegreeTwoTwelveFlexibleProfiles.Data row221Interface :=
  .ofExact row221At3 (by decide +kernel)

/-- Original row222, zero-based index221, joint; historical (2,1). -/
def row222 : DegreeTwoTwelveJointFiniteRowData row222Interface 2 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartExactSocles.row222_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row222Natural

noncomputable def row222Data : DegreeTwoTwelveFlexibleProfiles.Data row222Interface :=
  .ofExact row222 (by decide +kernel)

/-- Original row223, zero-based index222, joint; historical (2,1). -/
def row223At3 : DegreeTwoTwelveJointFiniteRowData row223Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row223AtThree_family
  natural := PrimitiveAffineDegreeTwoTwelveQuartetWordNaturalFamily.row223Natural

noncomputable def row223At3Data : DegreeTwoTwelveFlexibleProfiles.Data row223Interface :=
  .ofExact row223At3 (by decide +kernel)

/-- Original row225, zero-based index224, joint; historical (2,1). -/
def row225At3 : DegreeTwoTwelveJointFiniteRowData row225Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row225AtThree_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row225Natural

noncomputable def row225At3Data : DegreeTwoTwelveFlexibleProfiles.Data row225Interface :=
  .ofExact row225At3 (by decide +kernel)

/-- Original row250, zero-based index249, joint; historical (3,1). -/
def row250 : DegreeTwoTwelveJointFiniteRowData row250Interface 3 1 where
  topSocle := PrimitiveAffineDegreeTwoTwelveSecondPairChartSocles.row250_family
  natural := DegreeTwoTwelveRow94NaturalFamily.row250Natural

noncomputable def row250Data : DegreeTwoTwelveFlexibleProfiles.Data row250Interface :=
  .ofExact row250 (by decide +kernel)

end DegreeTwoTwelveSecondPairChartFinitePackages
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
