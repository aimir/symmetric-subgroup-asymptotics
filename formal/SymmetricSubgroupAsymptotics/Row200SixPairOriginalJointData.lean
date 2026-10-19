import SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow17NaturalFamily

/-! Selected physical pair receipt for the original row200 generators.
The six blocks and reference words were selected using unordered point-pair
orbits; all action claims below are checked on the retained original points. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row200SixPairOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun z := ⟨z.1.val + 6*z.2.val, by
    have h := z.2.val_lt
    omega⟩
  invFun x := (⟨x.val % 6, Nat.mod_lt _ (by decide)⟩,(x.val / 6 : Nat))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def topOne : Equiv.Perm (Fin 6) where
  toFun := ![0,5,2,1,4,3]
  invFun := ![0,3,2,5,4,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def topThree : Equiv.Perm (Fin 6) where
  toFun := ![5,2,1,4,3,0]
  invFun := ![5,2,1,4,3,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tops : Fin 4 → Equiv.Perm (Fin 6) :=
  ![1,topOne,Equiv.swap 1 3,topThree]

private theorem preserves : ∀ i, BinaryPairFrame.Preserves
    pointChart (row200Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame row200Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row200Generators tops preserves

def referenceWords : Fin 6 → row200Interface.top :=
  let t := closureGenerators row200Generators 1
  let c := closureGenerators row200Generators 3
  ![1,t⁻¹*c,c*t⁻¹*c,t*c,c*t*c,c]

instance top_pretransitive : MulAction.IsPretransitive pairFrame.top.range (Fin 6) :=
  OriginalSixPairNaturalJointData.top_pretransitive pairFrame referenceWords (by decide +kernel)

def flexibleData (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    DegreeTwoTwelveFlexibleProfiles.Data row200Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (OriginalSixPairNaturalJointData.jointData socle catalogue row200Interface pairFrame
      DegreeTwoTwelveRow17NaturalFamily.row200Natural) (by decide +kernel)

end SymmetricSubgroupAsymptotics.Row200SixPairOriginalJointData
