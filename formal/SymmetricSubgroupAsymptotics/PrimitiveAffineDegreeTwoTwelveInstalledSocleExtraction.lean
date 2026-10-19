import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveInstalledJoint

/-! Extract only the already proved installed normal families. Every
branch is the checked direct branch of InstalledJoint.socleFamily; the
unfinished RemainingData fallback is replaced by installed membership.
The capacity is the index of an actual proved family, not an assumed label. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveInstalledSocleExtraction
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows
open DegreeTwoTwelveInstalledJoint

set_option maxRecDepth 2048 in
def family (j : Fin 301) (hj : j ∈ installedSocles) :
    (catalogue.row j).finite.normalRegistry.QuotientSocleGeneratorFamily
      (catalogue.row j).kappa := by
  by_cases h0 : j = 0
  · subst j; exact PrimitiveAffineDegreeTwoTwelveRow1Resolution.finiteData.topSocle
  by_cases h299 : j = 299
  · subst j; exact DegreeTwoTwelveNaturalFinitePackages.row300.topSocle
  by_cases h300 : j = 300
  · subst j; exact DegreeTwoTwelveNaturalFinitePackages.row301.topSocle
  by_cases h16 : j = 16
  · subst j; exact PrimitiveAffineDegreeTwoTwelveRows17And19ImageSocles.row17TopSocle
  by_cases h18 : j = 18
  · subst j; exact DegreeTwoTwelveRow19FinitePackage.finiteData.topSocle
  by_cases h71 : j = 71
  · subst j; exact DegreeTwoTwelveRow72FinitePackage.finiteData.topSocle
  by_cases h130 : j = 130
  · subst j; exact DegreeTwoTwelveRow131FinitePackage.finiteData.topSocle
  by_cases h37 : j = 37
  · subst j; exact DegreeTwoTwelveMetacyclicFinitePackages.row38.topSocle
  by_cases h38 : j = 38
  · subst j; exact DegreeTwoTwelveMetacyclicFinitePackages.row39.topSocle
  by_cases h41 : j = 41
  · subst j; exact DegreeTwoTwelveMetacyclicFinitePackages.row42.topSocle
  by_cases h78 : j = 78
  · subst j; exact DegreeTwoTwelveParitySignFinitePackages.row79.topSocle
  by_cases h80 : j = 80
  · subst j; exact DegreeTwoTwelveParitySignFinitePackages.row81.topSocle
  by_cases h124 : j = 124
  · subst j; exact DegreeTwoTwelveParitySignFinitePackages.row125.topSocle
  by_cases h10 : j = 10
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row11.topSocle
  by_cases h11 : j = 11
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row12.topSocle
  by_cases h13 : j = 13
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row14.topSocle
  by_cases h115 : j = 115
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row116.topSocle
  by_cases h118 : j = 118
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row119.topSocle
  by_cases h119 : j = 119
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row120.topSocle
  by_cases h166 : j = 166
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row167.topSocle
  by_cases h168 : j = 168
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row169.topSocle
  by_cases h169 : j = 169
  · subst j; exact DegreeTwoTwelveSplitMetacyclicFinitePackages.row170.topSocle
  by_cases h1 : j = 1
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row2.topSocle
  by_cases h4 : j = 4
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row5.topSocle
  by_cases h12 : j = 12
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row13.topSocle
  by_cases h14 : j = 14
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row15.topSocle
  by_cases h15 : j = 15
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row16.topSocle
  by_cases h17 : j = 17
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row18.topSocle
  by_cases h27 : j = 27
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row28.topSocle
  by_cases h69 : j = 69
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row70.topSocle
  by_cases h70 : j = 70
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row71.topSocle
  by_cases h72 : j = 72
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row73.topSocle
  by_cases h117 : j = 117
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row118.topSocle
  by_cases h120 : j = 120
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row121.topSocle
  by_cases h129 : j = 129
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row130.topSocle
  by_cases h155 : j = 155
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row156.topSocle
  by_cases h216 : j = 216
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row217.topSocle
  by_cases h28 : j = 28
  · subst j; exact DegreeTwoTwelveQuaternaryImageFinitePackages.row29.topSocle
  by_cases h30 : j = 30
  · subst j; exact DegreeTwoTwelveQuaternaryImageFinitePackages.row31.topSocle
  by_cases h54 : j = 54
  · subst j; exact DegreeTwoTwelveQuaternaryImageFinitePackages.row55.topSocle
  by_cases h93 : j = 93
  · subst j; exact DegreeTwoTwelveRow94FinitePackage.finiteData.topSocle
  by_cases h132 : j = 132
  · subst j; exact DegreeTwoTwelveAugmentationFinitePackages.row133.topSocle
  by_cases h174 : j = 174
  · subst j; exact DegreeTwoTwelveAugmentationFinitePackages.row175.topSocle
  by_cases h177 : j = 177
  · subst j; exact DegreeTwoTwelveAugmentationFinitePackages.row178.topSocle
  by_cases h175 : j = 175
  · subst j; exact DegreeTwoTwelveRow176FinitePackage.finitePackage.topSocle
  by_cases h193 : j = 193
  · subst j; exact DegreeTwoTwelveFullTernaryFinitePackages.row194.topSocle
  by_cases h230 : j = 230
  · subst j; exact DegreeTwoTwelveFullTernaryFinitePackages.row231.topSocle
  by_cases h232 : j = 232
  · subst j; exact DegreeTwoTwelveRow233FinitePackage.finitePackage.topSocle
  by_cases h233 : j = 233
  · subst j; exact DegreeTwoTwelveRows234And258FinitePackages.row234.topSocle
  by_cases h257 : j = 257
  · subst j; exact DegreeTwoTwelveRows234And258FinitePackages.row258.topSocle
  by_cases h19 : j = 19
  · subst j; exact DegreeTwoTwelveDiagonalTernaryFinitePackages.row20.topSocle
  by_cases h42 : j = 42
  · subst j; exact DegreeTwoTwelveDiagonalTernaryFinitePackages.row43.topSocle
  by_cases h43 : j = 43
  · subst j; exact DegreeTwoTwelveDiagonalTernaryFinitePackages.row44.topSocle
  by_cases h44 : j = 44
  · subst j; exact DegreeTwoTwelveDiagonalTernaryFinitePackages.row45.topSocle
  by_cases h82 : j = 82
  · subst j; exact DegreeTwoTwelveDiagonalTernaryFinitePackages.row83.topSocle
  by_cases h3 : j = 3
  · subst j; exact DegreeTwoTwelveCocycleFinitePackages.row4.topSocle
  by_cases h131 : j = 131
  · subst j; exact DegreeTwoTwelveCocycleFinitePackages.row132.topSocle
  by_cases h176 : j = 176
  · subst j; exact DegreeTwoTwelveCocycleFinitePackages.row177.topSocle
  by_cases hsign210 : j = 210
  · subst j; exact DegreeTwoTwelveFullParitySignFinitePackages.row211.topSocle
  by_cases hsign244 : j = 244
  · subst j; exact DegreeTwoTwelveBinarySignFinitePackages.row245.topSocle
  by_cases hsign247 : j = 247
  · subst j; exact DegreeTwoTwelveFullParitySignFinitePackages.row248.topSocle
  by_cases hsign263 : j = 263
  · subst j; exact DegreeTwoTwelveBinarySignFinitePackages.row264.topSocle
  by_cases hsign266 : j = 266
  · subst j; exact DegreeTwoTwelveBinarySignFinitePackages.row267.topSocle
  by_cases hsign273 : j = 273
  · subst j; exact DegreeTwoTwelveBinarySignFinitePackages.row274.topSocle
  by_cases hsign288 : j = 288
  · subst j; exact DegreeTwoTwelveBinarySignFinitePackages.row289.topSocle
  by_cases hsub40 : j = 40
  · subst j; exact DegreeTwoTwelveSignedSubgroupFinitePackages.row41.topSocle
  by_cases hsub77 : j = 77
  · subst j; exact DegreeTwoTwelveSignedSubgroupFinitePackages.row78.topSocle
  by_cases hsub214 : j = 214
  · subst j; exact DegreeTwoTwelveSignedSubgroupFinitePackages.row215.topSocle
  by_cases hsub242 : j = 242
  · subst j; exact DegreeTwoTwelveSignedSubgroupFinitePackages.row243.topSocle
  by_cases hsub243 : j = 243
  · subst j; exact DegreeTwoTwelveSignedSubgroupFinitePackages.row244.topSocle
  by_cases hsub265 : j = 265
  · subst j; exact DegreeTwoTwelveSignedSubgroupFinitePackages.row266.topSocle
  by_cases hsub86 : j = 86
  · subst j; exact DegreeTwoTwelveSixPairImageFinitePackages.row87.topSocle
  by_cases hsub133 : j = 133
  · subst j; exact DegreeTwoTwelveSixPairImageFinitePackages.row134.topSocle
  by_cases hsub218 : j = 218
  · subst j; exact DegreeTwoTwelveSixPairImageFinitePackages.row219.topSocle
  by_cases hsub292 : j = 292
  · subst j; exact DegreeTwoTwelveSixPairImageFinitePackages.row293.topSocle
  by_cases hsub270 : j = 270
  · subst j; exact DegreeTwoTwelveAlternatingSignFinitePackage.row271.topSocle
  by_cases hpair2 : j = 2
  · subst j; exact DegreeTwoTwelvePairImageFinitePackages.row3.topSocle
  by_cases hpair88 : j = 88
  · subst j; exact DegreeTwoTwelvePairImageFinitePackages.row89.topSocle
  by_cases hpair90 : j = 90
  · subst j; exact DegreeTwoTwelvePairImageFinitePackages.row91.topSocle
  by_cases hpair105 : j = 105
  · subst j; exact DegreeTwoTwelvePairImageFinitePackages.row106.topSocle
  by_cases hpair134 : j = 134
  · subst j; exact DegreeTwoTwelvePairImageFinitePackages.row135.topSocle
  by_cases hpair142 : j = 142
  · subst j; exact DegreeTwoTwelvePairImageFinitePackages.row143.topSocle
  by_cases hpair192 : j = 192
  · subst j; exact DegreeTwoTwelvePairImageFinitePackages.row193.topSocle
  by_cases hpair234 : j = 234
  · subst j; exact DegreeTwoTwelvePairImageFinitePackages.row235.topSocle
  by_cases hchart50 : j = 50
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row51.topSocle
  by_cases hchart85 : j = 85
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row86.topSocle
  by_cases hchart140 : j = 140
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row141.topSocle
  by_cases hchart141 : j = 141
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row142.topSocle
  by_cases hchart184 : j = 184
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row185.topSocle
  by_cases hchart185 : j = 185
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row186.topSocle
  by_cases hchart188 : j = 188
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row189.topSocle
  by_cases hchart221 : j = 221
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row222.topSocle
  by_cases hchart249 : j = 249
  · subst j; exact DegreeTwoTwelveSecondPairChartFinitePackages.row250.topSocle
  have hnot : j ∉ installedSocles := by
    simpa only [installedSocles, Finset.mem_insert, Finset.mem_singleton, not_or] using
      (show j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3 ∧ j ≠ 4 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 12 ∧ j ≠ 13 ∧ j ≠ 14 ∧ j ≠ 15 ∧ j ≠ 16 ∧ j ≠ 17 ∧ j ≠ 18 ∧ j ≠ 19 ∧ j ≠ 27 ∧ j ≠ 28 ∧ j ≠ 30 ∧ j ≠ 37 ∧ j ≠ 38 ∧ j ≠ 40 ∧ j ≠ 41 ∧ j ≠ 42 ∧ j ≠ 43 ∧ j ≠ 44 ∧ j ≠ 50 ∧ j ≠ 54 ∧ j ≠ 69 ∧ j ≠ 70 ∧ j ≠ 71 ∧ j ≠ 72 ∧ j ≠ 77 ∧ j ≠ 78 ∧ j ≠ 80 ∧ j ≠ 82 ∧ j ≠ 85 ∧ j ≠ 86 ∧ j ≠ 88 ∧ j ≠ 90 ∧ j ≠ 93 ∧ j ≠ 105 ∧ j ≠ 115 ∧ j ≠ 117 ∧ j ≠ 118 ∧ j ≠ 119 ∧ j ≠ 120 ∧ j ≠ 124 ∧ j ≠ 129 ∧ j ≠ 130 ∧ j ≠ 131 ∧ j ≠ 132 ∧ j ≠ 133 ∧ j ≠ 134 ∧ j ≠ 140 ∧ j ≠ 141 ∧ j ≠ 142 ∧ j ≠ 155 ∧ j ≠ 166 ∧ j ≠ 168 ∧ j ≠ 169 ∧ j ≠ 174 ∧ j ≠ 175 ∧ j ≠ 176 ∧ j ≠ 177 ∧ j ≠ 184 ∧ j ≠ 185 ∧ j ≠ 188 ∧ j ≠ 192 ∧ j ≠ 193 ∧ j ≠ 210 ∧ j ≠ 214 ∧ j ≠ 216 ∧ j ≠ 218 ∧ j ≠ 221 ∧ j ≠ 230 ∧ j ≠ 232 ∧ j ≠ 233 ∧ j ≠ 234 ∧ j ≠ 242 ∧ j ≠ 243 ∧ j ≠ 244 ∧ j ≠ 247 ∧ j ≠ 249 ∧ j ≠ 257 ∧ j ≠ 263 ∧ j ≠ 265 ∧ j ≠ 266 ∧ j ≠ 270 ∧ j ≠ 273 ∧ j ≠ 288 ∧ j ≠ 292 ∧ j ≠ 299 ∧ j ≠ 300 from
        ⟨h0, h1, hpair2, h3, h4, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h27, h28, h30, h37, h38, hsub40, h41, h42, h43, h44, hchart50, h54, h69, h70, h71, h72, hsub77, h78, h80, h82, hchart85, hsub86, hpair88, hpair90, h93, hpair105, h115, h117, h118, h119, h120, h124, h129, h130, h131, h132, hsub133, hpair134, hchart140, hchart141, hpair142, h155, h166, h168, h169, h174, h175, h176, h177, hchart184, hchart185, hchart188, hpair192, h193, hsign210, hsub214, h216, hsub218, hchart221, h230, h232, h233, hpair234, hsub242, hsub243, hsign244, hsign247, hchart249, h257, hsign263, hsub265, hsign266, hsub270, hsign273, hsign288, hsub292, h299, h300⟩)

  exact False.elim (hnot hj)

/-- A proved equality of the index transports the existing actual family. -/
def family_one (j : Fin 301) (hj : j ∈ installedSocles)
    (h : (catalogue.row j).kappa=1) :
    (catalogue.row j).finite.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  h ▸ family j hj

end DegreeTwoTwelveInstalledSocleExtraction
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
