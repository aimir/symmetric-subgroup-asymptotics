import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoConcretePilotWiring

/-!
Preserve the already constructed exact packages while allowing other
original joint actions to use any proved admissible parameter pair.
The remaining data is still a collection of finite original-top bounds,
not a final counting estimate or an assumed capacity theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveFlexibleInstalledJoint

open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveFlexibleProfiles

/-- Original entries with complete exact packages reused below. -/
def exactIndices : Finset (Fin 301) := {0, 1, 3, 4, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 27, 28, 30, 37, 38, 41, 42, 43, 44, 54, 69, 70, 71, 72, 78, 80, 82, 93, 115, 117, 118, 119, 120, 124, 129, 130, 131, 132, 155, 166, 168, 169, 174, 175, 176, 177, 193, 216, 230, 232, 233, 257, 299, 300}

/-- Each selected package retains both original stored capacities. -/
noncomputable def exactPackage (j : Fin 301) (hj : j ∈ exactIndices) :
    Data (catalogue.row j).finite := by
  apply Classical.choice
  simp only [exactIndices, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (0 : Fin 301)).finite)
      (kappa := (catalogue.row (0 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (0 : Fin 301)).sectionCap)
      { topSocle := PrimitiveAffineDegreeTwoTwelveRow1Resolution.finiteData.topSocle
        natural := PrimitiveAffineDegreeTwoTwelveRow1Resolution.finiteData.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (1 : Fin 301)).finite)
      (kappa := (catalogue.row (1 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (1 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row2.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row2.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (3 : Fin 301)).finite)
      (kappa := (catalogue.row (3 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (3 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCocycleFinitePackages.row4.topSocle
        natural := DegreeTwoTwelveCocycleFinitePackages.row4.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (4 : Fin 301)).finite)
      (kappa := (catalogue.row (4 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (4 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row5.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row5.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (10 : Fin 301)).finite)
      (kappa := (catalogue.row (10 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (10 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row11.topSocle
        natural := DegreeTwoTwelveSharedNaturalWitnesses.row11Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (11 : Fin 301)).finite)
      (kappa := (catalogue.row (11 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (11 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row12.topSocle
        natural := DegreeTwoTwelveSharedNaturalWitnesses.row12Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (12 : Fin 301)).finite)
      (kappa := (catalogue.row (12 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (12 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row13.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row13.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (13 : Fin 301)).finite)
      (kappa := (catalogue.row (13 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (13 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row14.topSocle
        natural := DegreeTwoTwelveSharedNaturalWitnesses.row14Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (14 : Fin 301)).finite)
      (kappa := (catalogue.row (14 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (14 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row15.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row15.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (15 : Fin 301)).finite)
      (kappa := (catalogue.row (15 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (15 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row16.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row16.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (16 : Fin 301)).finite)
      (kappa := (catalogue.row (16 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (16 : Fin 301)).sectionCap)
      { topSocle := PrimitiveAffineDegreeTwoTwelveRows17And19ImageSocles.row17TopSocle
        natural := DegreeTwoTwelveRow17FinitePackage.finiteData.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (17 : Fin 301)).finite)
      (kappa := (catalogue.row (17 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (17 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row18.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row18.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (18 : Fin 301)).finite)
      (kappa := (catalogue.row (18 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (18 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveRow19FinitePackage.finiteData.topSocle
        natural := DegreeTwoTwelveRow19FinitePackage.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (19 : Fin 301)).finite)
      (kappa := (catalogue.row (19 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (19 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveDiagonalTernaryFinitePackages.row20.topSocle
        natural := DegreeTwoTwelveRow20NaturalFamily.row20Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (27 : Fin 301)).finite)
      (kappa := (catalogue.row (27 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (27 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row28.topSocle
        natural := DegreeTwoTwelveSharedNaturalWitnesses.row28Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (28 : Fin 301)).finite)
      (kappa := (catalogue.row (28 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (28 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveQuaternaryImageFinitePackages.row29.topSocle
        natural := DegreeTwoTwelveSharedNaturalWitnesses.row29Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (30 : Fin 301)).finite)
      (kappa := (catalogue.row (30 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (30 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveQuaternaryImageFinitePackages.row31.topSocle
        natural := DegreeTwoTwelveQuaternaryImageFinitePackages.row31.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (37 : Fin 301)).finite)
      (kappa := (catalogue.row (37 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (37 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveMetacyclicFinitePackages.row38.topSocle
        natural := DegreeTwoTwelveRow19CyclicFamily.row38Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (38 : Fin 301)).finite)
      (kappa := (catalogue.row (38 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (38 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveMetacyclicFinitePackages.row39.topSocle
        natural := DegreeTwoTwelveRow19CyclicFamily.row39Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (41 : Fin 301)).finite)
      (kappa := (catalogue.row (41 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (41 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveMetacyclicFinitePackages.row42.topSocle
        natural := DegreeTwoTwelveRow19CyclicFamily.row42Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (42 : Fin 301)).finite)
      (kappa := (catalogue.row (42 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (42 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveDiagonalTernaryFinitePackages.row43.topSocle
        natural := DegreeTwoTwelveRow20NaturalFamily.row43Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (43 : Fin 301)).finite)
      (kappa := (catalogue.row (43 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (43 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveDiagonalTernaryFinitePackages.row44.topSocle
        natural := DegreeTwoTwelveRow20NaturalFamily.row44Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (44 : Fin 301)).finite)
      (kappa := (catalogue.row (44 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (44 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveDiagonalTernaryFinitePackages.row45.topSocle
        natural := DegreeTwoTwelveSharedNaturalWitnesses.row45Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (54 : Fin 301)).finite)
      (kappa := (catalogue.row (54 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (54 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveQuaternaryImageFinitePackages.row55.topSocle
        natural := DegreeTwoTwelveThreeBlockNaturalFamily.row55Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (69 : Fin 301)).finite)
      (kappa := (catalogue.row (69 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (69 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row70.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row70.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (70 : Fin 301)).finite)
      (kappa := (catalogue.row (70 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (70 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row71.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row71.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (71 : Fin 301)).finite)
      (kappa := (catalogue.row (71 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (71 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveRow72FinitePackage.finiteData.topSocle
        natural := DegreeTwoTwelveRow72PolynomialFamily.row72Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (72 : Fin 301)).finite)
      (kappa := (catalogue.row (72 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (72 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row73.topSocle
        natural := DegreeTwoTwelveRow17NaturalFamily.row73Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (78 : Fin 301)).finite)
      (kappa := (catalogue.row (78 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (78 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveParitySignFinitePackages.row79.topSocle
        natural := DegreeTwoTwelveRow19CyclicFamily.row79Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (80 : Fin 301)).finite)
      (kappa := (catalogue.row (80 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (80 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveParitySignFinitePackages.row81.topSocle
        natural := DegreeTwoTwelveRow19CyclicFamily.row81Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (82 : Fin 301)).finite)
      (kappa := (catalogue.row (82 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (82 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveDiagonalTernaryFinitePackages.row83.topSocle
        natural := DegreeTwoTwelveSharedNaturalWitnesses.row83Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (93 : Fin 301)).finite)
      (kappa := (catalogue.row (93 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (93 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveRow94FinitePackage.finiteData.topSocle
        natural := DegreeTwoTwelveRow94NaturalFamily.row94Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (115 : Fin 301)).finite)
      (kappa := (catalogue.row (115 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (115 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row116.topSocle
        natural := DegreeTwoTwelveRow72PolynomialFamily.row116Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (117 : Fin 301)).finite)
      (kappa := (catalogue.row (117 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (117 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row118.topSocle
        natural := DegreeTwoTwelveRow17NaturalFamily.row118Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (118 : Fin 301)).finite)
      (kappa := (catalogue.row (118 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (118 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row119.topSocle
        natural := DegreeTwoTwelveRow72PolynomialFamily.row119Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (119 : Fin 301)).finite)
      (kappa := (catalogue.row (119 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (119 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row120.topSocle
        natural := DegreeTwoTwelveRow72PolynomialFamily.row120Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (120 : Fin 301)).finite)
      (kappa := (catalogue.row (120 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (120 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row121.topSocle
        natural := DegreeTwoTwelveRow17NaturalFamily.row121Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (124 : Fin 301)).finite)
      (kappa := (catalogue.row (124 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (124 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveParitySignFinitePackages.row125.topSocle
        natural := DegreeTwoTwelveRow19CyclicFamily.row125Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (129 : Fin 301)).finite)
      (kappa := (catalogue.row (129 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (129 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row130.topSocle
        natural := DegreeTwoTwelveCoprimeSplitFinitePackages.row130.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (130 : Fin 301)).finite)
      (kappa := (catalogue.row (130 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (130 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveRow131FinitePackage.finiteData.topSocle
        natural := DegreeTwoTwelveRow131CyclicFamily.row131Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (131 : Fin 301)).finite)
      (kappa := (catalogue.row (131 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (131 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCocycleFinitePackages.row132.topSocle
        natural := PrimitiveAffineDegreeTwoTwelveTernaryAlternatingNaturalFamily.row132Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (132 : Fin 301)).finite)
      (kappa := (catalogue.row (132 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (132 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveAugmentationFinitePackages.row133.topSocle
        natural := PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row133Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (155 : Fin 301)).finite)
      (kappa := (catalogue.row (155 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (155 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row156.topSocle
        natural := DegreeTwoTwelveRow72PolynomialFamily.row156Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (166 : Fin 301)).finite)
      (kappa := (catalogue.row (166 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (166 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row167.topSocle
        natural := DegreeTwoTwelveRow131CyclicFamily.row167Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (168 : Fin 301)).finite)
      (kappa := (catalogue.row (168 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (168 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row169.topSocle
        natural := DegreeTwoTwelveRow131CyclicFamily.row169Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (169 : Fin 301)).finite)
      (kappa := (catalogue.row (169 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (169 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveSplitMetacyclicFinitePackages.row170.topSocle
        natural := DegreeTwoTwelveRow131CyclicFamily.row170Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (174 : Fin 301)).finite)
      (kappa := (catalogue.row (174 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (174 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveAugmentationFinitePackages.row175.topSocle
        natural := DegreeTwoTwelveRow72PolynomialFamily.row175Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (175 : Fin 301)).finite)
      (kappa := (catalogue.row (175 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (175 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveRow176FinitePackage.finitePackage.topSocle
        natural := PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row176Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (176 : Fin 301)).finite)
      (kappa := (catalogue.row (176 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (176 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCocycleFinitePackages.row177.topSocle
        natural := DegreeTwoTwelveRow17NaturalFamily.row177Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (177 : Fin 301)).finite)
      (kappa := (catalogue.row (177 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (177 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveAugmentationFinitePackages.row178.topSocle
        natural := DegreeTwoTwelveRow17NaturalFamily.row178Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (193 : Fin 301)).finite)
      (kappa := (catalogue.row (193 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (193 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveFullTernaryFinitePackages.row194.topSocle
        natural := PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row194Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (216 : Fin 301)).finite)
      (kappa := (catalogue.row (216 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (216 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveCoprimeSplitFinitePackages.row217.topSocle
        natural := DegreeTwoTwelveRow131CyclicFamily.row217Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (230 : Fin 301)).finite)
      (kappa := (catalogue.row (230 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (230 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveFullTernaryFinitePackages.row231.topSocle
        natural := DegreeTwoTwelveRow131CyclicFamily.row231Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (232 : Fin 301)).finite)
      (kappa := (catalogue.row (232 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (232 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveRow233FinitePackage.finitePackage.topSocle
        natural := DegreeTwoTwelveRow17NaturalFamily.row233Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (233 : Fin 301)).finite)
      (kappa := (catalogue.row (233 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (233 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveRows234And258FinitePackages.row234.topSocle
        natural := PrimitiveAffineDegreeTwoTwelveRow133NaturalFamily.row234Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (257 : Fin 301)).finite)
      (kappa := (catalogue.row (257 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (257 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveRows234And258FinitePackages.row258.topSocle
        natural := DegreeTwoTwelveRow131CyclicFamily.row258Natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (299 : Fin 301)).finite)
      (kappa := (catalogue.row (299 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (299 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveNaturalFinitePackages.row300.topSocle
        natural := DegreeTwoTwelveNaturalFinitePackages.row300.natural } (by decide +kernel)
  · refine ⟨?_⟩
    exact Data.ofExact (D := (catalogue.row (300 : Fin 301)).finite)
      (kappa := (catalogue.row (300 : Fin 301)).kappa)
      (sectionCap := (catalogue.row (300 : Fin 301)).sectionCap)
      { topSocle := DegreeTwoTwelveNaturalFinitePackages.row301.topSocle
        natural := DegreeTwoTwelveSharedNaturalWitnesses.row301Natural } (by decide +kernel)

structure RemainingData : Type 1 where
  row : ∀ j : Fin 301, j ∉ exactIndices →
    (catalogue.row j).branch = .joint → Data (catalogue.row j).finite

namespace RemainingData

noncomputable def jointPackage (D : RemainingData) (j : Fin 301)
    (hbranch : (catalogue.row j).branch = .joint) : Data (catalogue.row j).finite :=
  if hj : j ∈ exactIndices then exactPackage j hj else D.row j hj hbranch

/-- Complete the same original catalogue with alternate proved profiles.
All non-joint branches retain their existing exact resolutions. -/
noncomputable def resolution (D : RemainingData)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature) :
    DegreeTwoTwelvePairTopCatalogueResolution catalogue := by
  intro j p realization
  cases hbranch : (catalogue.row j).branch with
  | joint =>
    exact (D.jointPackage j hbranch).resolvedRow hZmud lit
      (catalogue.row j).expectedProfiles realization
  | core =>
    exact DegreeTwoTwelvePairedSixOriginalQuotients.exceptionalCatalogueData.coreResolvedRow
      hZmud lit j realization hbranch
  | ternary =>
    exact (degreeTwoFourTernaryCatalogueCompression
      PrimitiveAffineDegreeTwoFourTernaryAffineWitnesses.compressionPackages
      j p realization hbranch).resolvedRow hZmud lit
  | paired =>
    exact DegreeTwoTwelvePairedSixOriginalQuotients.exceptionalCatalogueData.pairedResolvedRow
      hZmud lit j realization hbranch

end RemainingData

end DegreeTwoTwelveFlexibleInstalledJoint
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
