import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow176FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveAugmentationFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow94FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveQuaternaryImageFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCoprimeSplitFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSplitMetacyclicFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow20NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow265NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow94NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveParitySignFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow19CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow72FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveNaturalFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow72PolynomialFamily

/-!
# Install proved fields of the original joint twelve-point catalogue

The cyclic first row and the natural alternating/symmetric rows supply
complete packages. Shared literal orbit witnesses independently supply
further natural-module fields. The remaining structure requests only the
unproved fields, always at the original catalogue's exact stored capacities.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveInstalledJoint

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

def installedSocles : Finset (Fin 301) := {0, 1, 4, 10, 11, 12, 13, 14, 15, 16, 17, 18, 27, 28, 30, 37, 38, 41, 54, 69, 70, 71, 72, 78, 80, 93, 115, 117, 118, 119, 120, 124, 129, 130, 132, 155, 166, 168, 169, 174, 175, 177, 216, 299, 300}

def installedNaturals : Finset (Fin 301) := {0, 1, 2, 4, 6, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 27, 28, 30, 32, 33, 34, 35, 37, 38, 41, 42, 43, 44, 52, 54, 55, 56, 57, 59, 69, 70, 71, 72, 73, 74, 75, 78, 80, 82, 86, 88, 89, 90, 93, 94, 95, 96, 99, 100, 104, 105, 107, 108, 112, 115, 117, 118, 119, 120, 122, 124, 129, 130, 132, 140, 143, 149, 150, 155, 163, 165, 166, 168, 169, 174, 175, 176, 177, 179, 181, 182, 183, 184, 186, 188, 189, 190, 193, 199, 201, 203, 204, 205, 206, 208, 210, 212, 216, 218, 220, 221, 224, 225, 227, 228, 229, 230, 232, 233, 238, 244, 246, 247, 249, 250, 251, 252, 253, 256, 257, 262, 263, 264, 266, 267, 268, 272, 273, 274, 275, 276, 277, 278, 280, 282, 283, 284, 287, 288, 289, 290, 291, 293, 295, 296, 297, 298, 299, 300}

structure RemainingData : Type 1 where
  socle : ∀ j : Fin 301, j ∉ installedSocles →
    (catalogue.row j).branch = .joint →
    (catalogue.row j).finite.normalRegistry.QuotientSocleGeneratorFamily
      (catalogue.row j).kappa
  natural : ∀ j : Fin 301, j ∉ installedNaturals →
    (catalogue.row j).branch = .joint →
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) (catalogue.row j).finite.top (Fin 12))
      (catalogue.row j).sectionCap

namespace RemainingData

noncomputable def socleFamily (D : RemainingData) (j : Fin 301)
    (hbranch : (catalogue.row j).branch = .joint) :
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
  exact D.socle j (by simp [installedSocles, h175, h132, h174, h177, h28, h30, h54, h93, h1, h4, h12, h14, h15, h17, h27, h69, h70, h72, h117, h120, h129, h155, h216, h10, h11, h13, h115, h118, h119, h166, h168, h169, h0, h16, h18, h37, h38, h41, h71, h78, h80, h124, h130, h299, h300]) hbranch

theorem naturalBound (D : RemainingData) (j : Fin 301)
    (hbranch : (catalogue.row j).branch = .joint) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) (catalogue.row j).finite.top (Fin 12))
      (catalogue.row j).sectionCap := by
  by_cases h0 : j = 0
  · subst j; exact PrimitiveAffineDegreeTwoTwelveRow1Resolution.finiteData.natural
  by_cases h10 : j = 10
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row11Natural
  by_cases h11 : j = 11
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row12Natural
  by_cases h13 : j = 13
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row14Natural
  by_cases h27 : j = 27
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row28Natural
  by_cases h28 : j = 28
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row29Natural
  by_cases h33 : j = 33
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row34Natural
  by_cases h44 : j = 44
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row45Natural
  by_cases h52 : j = 52
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row53Natural
  by_cases h57 : j = 57
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row58Natural
  by_cases h59 : j = 59
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row60Natural
  by_cases h82 : j = 82
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row83Natural
  by_cases h86 : j = 86
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row87Natural
  by_cases h88 : j = 88
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row89Natural
  by_cases h90 : j = 90
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row91Natural
  by_cases h104 : j = 104
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row105Natural
  by_cases h107 : j = 107
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row108Natural
  by_cases h108 : j = 108
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row109Natural
  by_cases h112 : j = 112
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row113Natural
  by_cases h201 : j = 201
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row202Natural
  by_cases h218 : j = 218
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row219Natural
  by_cases h284 : j = 284
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row285Natural
  by_cases h299 : j = 299
  · subst j; exact DegreeTwoTwelveNaturalFinitePackages.row300.natural
  by_cases h300 : j = 300
  · subst j; exact DegreeTwoTwelveSharedNaturalWitnesses.row301Natural
  by_cases h130 : j = 130
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row131Natural
  by_cases h166 : j = 166
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row167Natural
  by_cases h168 : j = 168
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row169Natural
  by_cases h169 : j = 169
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row170Natural
  by_cases h208 : j = 208
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row209Natural
  by_cases h210 : j = 210
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row211Natural
  by_cases h216 : j = 216
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row217Natural
  by_cases h230 : j = 230
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row231Natural
  by_cases h244 : j = 244
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row245Natural
  by_cases h246 : j = 246
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row247Natural
  by_cases h247 : j = 247
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row248Natural
  by_cases h257 : j = 257
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row258Natural
  by_cases h262 : j = 262
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row263Natural
  by_cases h263 : j = 263
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row264Natural
  by_cases h266 : j = 266
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row267Natural
  by_cases h273 : j = 273
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row274Natural
  by_cases h280 : j = 280
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row281Natural
  by_cases h288 : j = 288
  · subst j; exact DegreeTwoTwelveRow131CyclicFamily.row289Natural
  by_cases h71 : j = 71
  · subst j; exact DegreeTwoTwelveRow72PolynomialFamily.row72Natural
  by_cases h115 : j = 115
  · subst j; exact DegreeTwoTwelveRow72PolynomialFamily.row116Natural
  by_cases h118 : j = 118
  · subst j; exact DegreeTwoTwelveRow72PolynomialFamily.row119Natural
  by_cases h119 : j = 119
  · subst j; exact DegreeTwoTwelveRow72PolynomialFamily.row120Natural
  by_cases h155 : j = 155
  · subst j; exact DegreeTwoTwelveRow72PolynomialFamily.row156Natural
  by_cases h174 : j = 174
  · subst j; exact DegreeTwoTwelveRow72PolynomialFamily.row175Natural
  by_cases h212 : j = 212
  · subst j; exact DegreeTwoTwelveRow72PolynomialFamily.row213Natural
  by_cases h18 : j = 18
  · subst j; exact DegreeTwoTwelveRow19FinitePackage.natural
  by_cases h16 : j = 16
  · subst j; exact DegreeTwoTwelveRow17FinitePackage.finiteData.natural
  by_cases h37 : j = 37
  · subst j; exact DegreeTwoTwelveRow19CyclicFamily.row38Natural
  by_cases h38 : j = 38
  · subst j; exact DegreeTwoTwelveRow19CyclicFamily.row39Natural
  by_cases h41 : j = 41
  · subst j; exact DegreeTwoTwelveRow19CyclicFamily.row42Natural
  by_cases h78 : j = 78
  · subst j; exact DegreeTwoTwelveRow19CyclicFamily.row79Natural
  by_cases h80 : j = 80
  · subst j; exact DegreeTwoTwelveRow19CyclicFamily.row81Natural
  by_cases h124 : j = 124
  · subst j; exact DegreeTwoTwelveRow19CyclicFamily.row125Natural
  by_cases h34 : j = 34
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row35Natural
  by_cases h35 : j = 35
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row36Natural
  by_cases h72 : j = 72
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row73Natural
  by_cases h117 : j = 117
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row118Natural
  by_cases h120 : j = 120
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row121Natural
  by_cases h176 : j = 176
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row177Natural
  by_cases h177 : j = 177
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row178Natural
  by_cases h199 : j = 199
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row200Natural
  by_cases h232 : j = 232
  · subst j; exact DegreeTwoTwelveRow17NaturalFamily.row233Natural
  by_cases h93 : j = 93
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row94Natural
  by_cases h140 : j = 140
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row141Natural
  by_cases h149 : j = 149
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row150Natural
  by_cases h150 : j = 150
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row151Natural
  by_cases h184 : j = 184
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row185Natural
  by_cases h188 : j = 188
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row189Natural
  by_cases h220 : j = 220
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row221Natural
  by_cases h221 : j = 221
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row222Natural
  by_cases h224 : j = 224
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row225Natural
  by_cases h249 : j = 249
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row250Natural
  by_cases h291 : j = 291
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row292Natural
  by_cases h293 : j = 293
  · subst j; exact DegreeTwoTwelveRow94NaturalFamily.row294Natural
  by_cases h20 : j = 20
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row21Natural
  by_cases h54 : j = 54
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row55Natural
  by_cases h55 : j = 55
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row56Natural
  by_cases h56 : j = 56
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row57Natural
  by_cases h89 : j = 89
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row90Natural
  by_cases h94 : j = 94
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row95Natural
  by_cases h95 : j = 95
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row96Natural
  by_cases h96 : j = 96
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row97Natural
  by_cases h99 : j = 99
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row100Natural
  by_cases h100 : j = 100
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row101Natural
  by_cases h105 : j = 105
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row106Natural
  by_cases h143 : j = 143
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row144Natural
  by_cases h183 : j = 183
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row184Natural
  by_cases h186 : j = 186
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row187Natural
  by_cases h189 : j = 189
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row190Natural
  by_cases h190 : j = 190
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row191Natural
  by_cases h225 : j = 225
  · subst j; exact DegreeTwoTwelveThreeBlockNaturalFamily.row226Natural
  by_cases h264 : j = 264
  · subst j; exact DegreeTwoTwelveRow265NaturalFamily.row265Natural
  by_cases h272 : j = 272
  · subst j; exact DegreeTwoTwelveRow265NaturalFamily.row273Natural
  by_cases h274 : j = 274
  · subst j; exact DegreeTwoTwelveRow265NaturalFamily.row275Natural
  by_cases h275 : j = 275
  · subst j; exact DegreeTwoTwelveRow265NaturalFamily.row276Natural
  by_cases h282 : j = 282
  · subst j; exact DegreeTwoTwelveRow265NaturalFamily.row283Natural
  by_cases h283 : j = 283
  · subst j; exact DegreeTwoTwelveRow265NaturalFamily.row284Natural
  by_cases h289 : j = 289
  · subst j; exact DegreeTwoTwelveRow265NaturalFamily.row290Natural
  by_cases h290 : j = 290
  · subst j; exact DegreeTwoTwelveRow265NaturalFamily.row291Natural
  by_cases h19 : j = 19
  · subst j; exact DegreeTwoTwelveRow20NaturalFamily.row20Natural
  by_cases h42 : j = 42
  · subst j; exact DegreeTwoTwelveRow20NaturalFamily.row43Natural
  by_cases h43 : j = 43
  · subst j; exact DegreeTwoTwelveRow20NaturalFamily.row44Natural
  by_cases h163 : j = 163
  · subst j; exact DegreeTwoTwelveRow20NaturalFamily.row164Natural
  by_cases h203 : j = 203
  · subst j; exact DegreeTwoTwelveRow20NaturalFamily.row204Natural
  by_cases h204 : j = 204
  · subst j; exact DegreeTwoTwelveRow20NaturalFamily.row205Natural
  by_cases h205 : j = 205
  · subst j; exact DegreeTwoTwelveRow20NaturalFamily.row206Natural
  by_cases h238 : j = 238
  · subst j; exact DegreeTwoTwelveRow20NaturalFamily.row239Natural
  by_cases h1 : j = 1
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row2.natural
  by_cases h4 : j = 4
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row5.natural
  by_cases h12 : j = 12
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row13.natural
  by_cases h14 : j = 14
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row15.natural
  by_cases h15 : j = 15
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row16.natural
  by_cases h17 : j = 17
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row18.natural
  by_cases h69 : j = 69
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row70.natural
  by_cases h70 : j = 70
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row71.natural
  by_cases h129 : j = 129
  · subst j; exact DegreeTwoTwelveCoprimeSplitFinitePackages.row130.natural
  by_cases h30 : j = 30
  · subst j; exact DegreeTwoTwelveQuaternaryImageFinitePackages.row31.natural
  by_cases h228 : j = 228
  · subst j; exact PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row229Natural
  by_cases h250 : j = 250
  · subst j; exact PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row251Natural
  by_cases h251 : j = 251
  · subst j; exact PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row252Natural
  by_cases h252 : j = 252
  · subst j; exact PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row253Natural
  by_cases h267 : j = 267
  · subst j; exact PrimitiveAffineDegreeTwoTwelveDiagonalAlternatingNaturalFamily.row268Natural
  by_cases h132 : j = 132
  · subst j; exact PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row133Natural
  by_cases h175 : j = 175
  · subst j; exact PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row176Natural
  by_cases h193 : j = 193
  · subst j; exact PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row194Natural
  by_cases h233 : j = 233
  · subst j; exact PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row234Natural
  by_cases h165 : j = 165
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row166Natural
  by_cases h206 : j = 206
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row207Natural
  by_cases h227 : j = 227
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row228Natural
  by_cases h253 : j = 253
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row254Natural
  by_cases h179 : j = 179
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row180Natural
  by_cases h181 : j = 181
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row182Natural
  by_cases h268 : j = 268
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row269Natural
  by_cases h277 : j = 277
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row278Natural
  by_cases h278 : j = 278
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row279Natural
  by_cases h287 : j = 287
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row288Natural
  by_cases h295 : j = 295
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row296Natural
  by_cases h296 : j = 296
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row297Natural
  by_cases h297 : j = 297
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row298Natural
  by_cases h298 : j = 298
  · subst j; exact PrimitiveAffineDegreeTwoTwelveFiveCycleNaturalFamily.row299Natural
  by_cases h2 : j = 2
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row3Natural
  by_cases h6 : j = 6
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row7Natural
  by_cases h22 : j = 22
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row23Natural
  by_cases h23 : j = 23
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row24Natural
  by_cases h24 : j = 24
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row25Natural
  by_cases h32 : j = 32
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row33Natural
  by_cases h73 : j = 73
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row74Natural
  by_cases h74 : j = 74
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row75Natural
  by_cases h75 : j = 75
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row76Natural
  by_cases h122 : j = 122
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row123Natural
  by_cases h182 : j = 182
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row183Natural
  by_cases h229 : j = 229
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row230Natural
  by_cases h256 : j = 256
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row257Natural
  by_cases h276 : j = 276
  · subst j; exact PrimitiveAffineDegreeTwoTwelveTwoGeneratorNaturalFamily.row277Natural
  exact D.natural j (by simp only [installedNaturals, h2, h6, h22, h23, h24, h32, h73, h74, h75, h122, h182, h229, h256, h276, h179, h181, h268, h277, h278, h287, h295, h296, h297, h298, h165, h206, h227, h253, h132, h175, h193, h233, h228, h250, h251, h252, h267, h30, h1, h4, h12, h14, h15, h17, h69, h70, h129, h19, h42, h43, h163, h203, h204, h205, h238, Finset.mem_insert, Finset.mem_singleton, false_or, not_false_eq_true, h264, h272, h274, h275, h282, h283, h289, h290, h93, h140, h149, h150, h184, h188, h220, h221, h224, h249, h291, h293, h20, h54, h55, h56, h89, h94, h95, h96, h99, h100, h105, h143, h183, h186, h189, h190, h225, h34, h35, h72, h117, h120, h176, h177, h199, h232, h16, h18, h37, h38, h41, h78, h80, h124, h0, h10, h11, h13, h27, h28, h33, h44, h52, h57, h59, h71, h82, h86, h88, h90, h104, h107, h108, h112, h115, h118, h119, h130, h155, h166, h168, h169, h174, h201, h208, h210, h212, h216, h218, h230, h244, h246, h247, h257, h262, h263, h266, h273, h280, h284, h288, h299, h300]) hbranch

noncomputable def finiteCatalogue (D : RemainingData) :
    DegreeTwoTwelveJointFiniteCatalogueData catalogue where
  row j hbranch :=
    { topSocle := D.socleFamily j hbranch
      natural := D.naturalBound j hbranch }

end RemainingData
end DegreeTwoTwelveInstalledJoint
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
