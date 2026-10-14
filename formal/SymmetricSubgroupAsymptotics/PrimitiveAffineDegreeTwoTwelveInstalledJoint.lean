import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1Resolution
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveNaturalFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSharedNaturalWitnesses

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

def installedSocles : Finset (Fin 301) := {0, 299, 300}

def installedNaturals : Finset (Fin 301) := {0, 10, 11, 13, 27, 28, 33, 44, 52, 57, 59, 82, 86, 88, 90, 104, 107, 108, 112, 201, 218, 284, 299, 300}

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
  exact D.socle j (by simp [installedSocles, h0, h299, h300]) hbranch

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
  exact D.natural j (by simp [installedNaturals, h0, h10, h11, h13, h27, h28, h33, h44, h52, h57, h59, h82, h86, h88, h90, h104, h107, h108, h112, h201, h218, h284, h299, h300]) hbranch

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
