import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryAffineActionFacts
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryClosure

/-!
# The eight literal four-ternary witnesses from affine coordinates

Coordinate equivalences give the exact core orders, and the semidirect
product gives the exact top orders. The resulting literal witnesses feed
the existing common compression theorem and the actual ternary locator in
the 301-row catalogue.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoFourTernaryAffineWitnesses

open TernarySignedBlockCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoordinates
open PrimitiveAffineDegreeTwoFourTernaryBinaryCoordinates
open PrimitiveAffineDegreeTwoFourTernaryCoreCoordinates
open PrimitiveAffineDegreeTwoFourTernarySemidirectBinding
open SemidirectAbelianCentralizer
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def pairedCoreEquiv : Core 0 ≃ Scalar × Scalar where
  toFun v := (v.val 0, v.val 1)
  invFun p := ⟨![p.1, p.2, p.1, p.2], by
    change pairedProjection ![p.1, p.2, p.1, p.2] = ![p.1, p.2, p.1, p.2]
    funext i
    fin_cases i <;> rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    have h := congrArg (fun w : Vector => w i) v.property
    fin_cases i <;> exact h
  right_inv _ := rfl

def augmentationCoreEquiv : Core 2 ≃ Scalar × Scalar × Scalar where
  toFun v := (v.val 0, v.val 1, v.val 2)
  invFun p := ⟨![p.1, p.2.1, p.2.2, -(p.1 + p.2.1 + p.2.2)], by
    change augmentationProjection
      ![p.1, p.2.1, p.2.2, -(p.1 + p.2.1 + p.2.2)] =
      ![p.1, p.2.1, p.2.2, -(p.1 + p.2.1 + p.2.2)]
    funext i
    fin_cases i <;> rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    have h := congrArg (fun w : Vector => w i) v.property
    fin_cases i <;> exact h
  right_inv _ := rfl

def fullCoreEquiv : Core 3 ≃ Vector where
  toFun := Subtype.val
  invFun v := ⟨v, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem paired_core_card : Nat.card (Core 0) = 9 := by
  rw [Nat.card_congr pairedCoreEquiv, Nat.card_prod]
  norm_num [Scalar, Nat.card_zmod]

theorem augmentation_core_card : Nat.card (Core 2) = 27 := by
  rw [Nat.card_congr augmentationCoreEquiv, Nat.card_prod, Nat.card_prod]
  norm_num [Scalar, Nat.card_zmod]

theorem full_core_card : Nat.card (Core 3) = 81 := by
  rw [Nat.card_congr fullCoreEquiv]
  simp only [TernarySignedBlockCoordinates.Vector, Nat.card_fun, Nat.card_fin,
    Scalar, Nat.card_zmod]
  norm_num

theorem core_card (r : Fin 8) :
    Nat.card (Multiplicative (Core r)) = degreeTwoFourTernaryCoreOrder r := by
  rw [Nat.card_congr Multiplicative.toAdd]
  fin_cases r
  · exact paired_core_card
  · exact paired_core_card
  · exact augmentation_core_card
  · exact full_core_card
  · exact full_core_card
  · exact full_core_card
  · exact full_core_card
  · exact full_core_card

theorem original_top_card (r : Fin 8) :
    Nat.card (degreeTwoFourTernaryInterface r).top = degreeTwoFourTernaryTopOrder r := by
  calc
    Nat.card (degreeTwoFourTernaryInterface r).top = Nat.card (Model r) :=
      Nat.card_congr (affineEquiv r).toEquiv
    _ = Nat.card (Multiplicative (Core r) × Complement r) :=
      Nat.card_congr SemidirectProduct.equivProd
    _ = degreeTwoFourTernaryCoreOrder r * 2 ^ complementExponent r := by
      rw [Nat.card_prod, core_card, complement_card]
    _ = degreeTwoFourTernaryTopOrder r := by fin_cases r <;> decide +kernel

theorem original_core_card (r : Fin 8) :
    Nat.card (PrimitiveAffineDegreeTwoFourTernaryAffineActionFacts.topStructure r).core =
      degreeTwoFourTernaryCoreOrder r := by
  change Nat.card (originalProjection (affineEquiv r)).ker = _
  rw [originalTranslation_card, core_card]

noncomputable def literalWitness (r : Fin 8) : DegreeTwoFourTernaryLiteralWitness r where
  topStructure := PrimitiveAffineDegreeTwoFourTernaryAffineActionFacts.topStructure r
  top_card_eq := original_top_card r
  core_card_eq := original_core_card r

noncomputable def catalogueWitnesses : DegreeTwoFourTernaryCatalogueWitnesses where
  witness := literalWitness

noncomputable def compressionPackages : ∀ r : Fin 8,
    DegreeTwoTwelveFourTernaryCompressionPackage (degreeTwoFourTernaryInterface r) :=
  catalogueWitnesses.compressionPackages

noncomputable def catalogueCompression (j : Fin 301) (p : PreE7PairActionClass 12)
    (R : DegreeTwoPairTopRealization (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row j).finite p)
    (h : (DegreeTwoTwelvePairFiniteCatalogue.catalogue.row j).branch = .ternary) :
    DegreeTwoFourTernaryCompressionData p :=
  degreeTwoFourTernaryCatalogueCompression compressionPackages j p R h

end PrimitiveAffineDegreeTwoFourTernaryAffineWitnesses
end SymmetricSubgroupAsymptotics

end
