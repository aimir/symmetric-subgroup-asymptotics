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

def installedSocles : Finset (Fin 301) := {0, 16, 18, 37, 38, 41, 71, 78, 80, 124, 130, 299, 300}

def installedNaturals : Finset (Fin 301) := {0, 10, 11, 13, 16, 18, 27, 28, 33, 37, 38, 41, 44, 52, 57, 59, 71, 78, 80, 82, 86, 88, 90, 104, 107, 108, 112, 115, 118, 119, 124, 130, 155, 166, 168, 169, 174, 201, 208, 210, 212, 216, 218, 230, 244, 246, 247, 257, 262, 263, 266, 273, 280, 284, 288, 299, 300}

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
  exact D.socle j (by simp [installedSocles, h0, h16, h18, h37, h38, h41, h71, h78, h80, h124, h130, h299, h300]) hbranch

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
  exact D.natural j (by simp [installedNaturals, h16, h18, h37, h38, h41, h78, h80, h124, h0, h10, h11, h13, h27, h28, h33, h44, h52, h57, h59, h71, h82, h86, h88, h90, h104, h107, h108, h112, h115, h118, h119, h130, h155, h166, h168, h169, h174, h201, h208, h210, h212, h216, h218, h230, h244, h246, h247, h257, h262, h263, h266, h273, h280, h284, h288, h299, h300]) hbranch

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
