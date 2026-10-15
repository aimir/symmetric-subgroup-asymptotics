import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedAlternateSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131CyclicFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedTernaryFlipWordNaturalFamily

/-! Fourteen admissible alternate profiles, using actual original-action
quotient-socle bounds and the existing cap-one natural modules. The
historical profiles are retained as endpoint labels, not asserted equal. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSignedAlternateProfiles

open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows
open PrimitiveAffineDegreeTwoTwelveSignedAlternateSocles

def row46AtTwo : DegreeTwoTwelveFlexibleProfiles.Data row46Interface where
  kappa := 2
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row46AtTwo_family
    natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row46Natural }

def row173AtTwo : DegreeTwoTwelveFlexibleProfiles.Data row173Interface where
  kappa := 2
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row173AtTwo_family
    natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row173Natural }

def row35AtThree : DegreeTwoTwelveFlexibleProfiles.Data row35Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row35AtThree_family
    natural := DegreeTwoTwelveRow17NaturalFamily.row35Natural }

def row36AtThree : DegreeTwoTwelveFlexibleProfiles.Data row36Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row36AtThree_family
    natural := DegreeTwoTwelveRow17NaturalFamily.row36Natural }

def row80AtThree : DegreeTwoTwelveFlexibleProfiles.Data row80Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row80AtThree_family
    natural := PrimitiveAffineDegreeTwoTwelvePairedTernaryFlipWordNaturalFamily.row80Natural }

def row82AtThree : DegreeTwoTwelveFlexibleProfiles.Data row82Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row82AtThree_family
    natural := PrimitiveAffineDegreeTwoTwelvePairedTernaryFlipWordNaturalFamily.row82Natural }

def row84AtThree : DegreeTwoTwelveFlexibleProfiles.Data row84Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row84AtThree_family
    natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row84Natural }

def row209AtThree : DegreeTwoTwelveFlexibleProfiles.Data row209Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row209AtThree_family
    natural := DegreeTwoTwelveRow131CyclicFamily.row209Natural }

def row212AtThree : DegreeTwoTwelveFlexibleProfiles.Data row212Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row212AtThree_family
    natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row212Natural }

def row216AtThree : DegreeTwoTwelveFlexibleProfiles.Data row216Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row216AtThree_family
    natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row216Natural }

def row247AtThree : DegreeTwoTwelveFlexibleProfiles.Data row247Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row247AtThree_family
    natural := DegreeTwoTwelveRow131CyclicFamily.row247Natural }

def row249AtThree : DegreeTwoTwelveFlexibleProfiles.Data row249Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row249AtThree_family
    natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row249Natural }

def row262AtThree : DegreeTwoTwelveFlexibleProfiles.Data row262Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row262AtThree_family
    natural := PrimitiveAffineDegreeTwoTwelveTernaryBlockCycleNaturalFamily.row262Natural }

def row263AtThree : DegreeTwoTwelveFlexibleProfiles.Data row263Interface where
  kappa := 3
  sectionCap := 1
  parameters := by decide +kernel
  finite := {
    topSocle := row263AtThree_family
    natural := DegreeTwoTwelveRow131CyclicFamily.row263Natural }

def row46AtTwoResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (45 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (45 : Fin 301)).finite
      (catalogue.row (45 : Fin 301)).expectedProfiles p :=
  row46AtTwo.resolvedRow hZmud lit _ R

def row173AtTwoResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (172 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (172 : Fin 301)).finite
      (catalogue.row (172 : Fin 301)).expectedProfiles p :=
  row173AtTwo.resolvedRow hZmud lit _ R

def row35AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (34 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (34 : Fin 301)).finite
      (catalogue.row (34 : Fin 301)).expectedProfiles p :=
  row35AtThree.resolvedRow hZmud lit _ R

def row36AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (35 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (35 : Fin 301)).finite
      (catalogue.row (35 : Fin 301)).expectedProfiles p :=
  row36AtThree.resolvedRow hZmud lit _ R

def row80AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (79 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (79 : Fin 301)).finite
      (catalogue.row (79 : Fin 301)).expectedProfiles p :=
  row80AtThree.resolvedRow hZmud lit _ R

def row82AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (81 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (81 : Fin 301)).finite
      (catalogue.row (81 : Fin 301)).expectedProfiles p :=
  row82AtThree.resolvedRow hZmud lit _ R

def row84AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (83 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (83 : Fin 301)).finite
      (catalogue.row (83 : Fin 301)).expectedProfiles p :=
  row84AtThree.resolvedRow hZmud lit _ R

def row209AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (208 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (208 : Fin 301)).finite
      (catalogue.row (208 : Fin 301)).expectedProfiles p :=
  row209AtThree.resolvedRow hZmud lit _ R

def row212AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (211 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (211 : Fin 301)).finite
      (catalogue.row (211 : Fin 301)).expectedProfiles p :=
  row212AtThree.resolvedRow hZmud lit _ R

def row216AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (215 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (215 : Fin 301)).finite
      (catalogue.row (215 : Fin 301)).expectedProfiles p :=
  row216AtThree.resolvedRow hZmud lit _ R

def row247AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (246 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (246 : Fin 301)).finite
      (catalogue.row (246 : Fin 301)).expectedProfiles p :=
  row247AtThree.resolvedRow hZmud lit _ R

def row249AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (248 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (248 : Fin 301)).finite
      (catalogue.row (248 : Fin 301)).expectedProfiles p :=
  row249AtThree.resolvedRow hZmud lit _ R

def row262AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (261 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (261 : Fin 301)).finite
      (catalogue.row (261 : Fin 301)).expectedProfiles p :=
  row262AtThree.resolvedRow hZmud lit _ R

def row263AtThreeResolved (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization (catalogue.row (262 : Fin 301)).finite p) :
    DegreeTwoPairTopResolvedRow (catalogue.row (262 : Fin 301)).finite
      (catalogue.row (262 : Fin 301)).expectedProfiles p :=
  row263AtThree.resolvedRow hZmud lit _ R

end DegreeTwoTwelveSignedAlternateProfiles
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
