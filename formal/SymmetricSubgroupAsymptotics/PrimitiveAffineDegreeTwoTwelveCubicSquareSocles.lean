import SymmetricSubgroupAsymptotics.BinaryThreeQuartetCubicSquareSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow20NaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Literal original rows85 and164 share the scalar-Singer/cyclic-block
C3 x C3 model. All affine offsets and all original normal quotients remain
in the proof; a finite point chart does not replace a normal denominator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicSquareSocles
open BinaryThreeQuartetCubicSquareSocles
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

namespace Row85
def points : Fin 12 ≃ Fin 12 where
  toFun := ![0, 1, 2, 3, 10, 5, 9, 4, 11, 6, 7, 8]
  invFun := ![0, 1, 2, 3, 7, 5, 9, 10, 11, 6, 4, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lifts : Fin 3 → Model :=
  ![
⟨Multiplicative.ofAdd (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 2, BinaryThreeQuartetLiteralSocles.planeLabel.symm 0, BinaryThreeQuartetLiteralSocles.planeLabel.symm 2] : Vector),
    (Multiplicative.ofAdd 0, Multiplicative.ofAdd 0)⟩,
   ⟨Multiplicative.ofAdd (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 3, BinaryThreeQuartetLiteralSocles.planeLabel.symm 2, BinaryThreeQuartetLiteralSocles.planeLabel.symm 1] : Vector),
    (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)⟩,
   ⟨Multiplicative.ofAdd (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 3, BinaryThreeQuartetLiteralSocles.planeLabel.symm 2, BinaryThreeQuartetLiteralSocles.planeLabel.symm 1] : Vector),
    (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)⟩]

theorem bindings (i : Fin 3) : literalAction points (lifts i) = row85Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem original_quotientSocle (N : Subgroup Row85Top) [N.Normal] :
    SocleNormalGeneratorBound (Row85Top ⧸ N) 2 :=
  quotientSocle points lifts row85Generators bindings 1 2 rfl rfl N

def family : row85Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact original_quotientSocle N.1)

def rowData : DegreeTwoTwelveJointFiniteRowData row85Interface 2 1 where
  topSocle := family
  natural := PrimitiveAffineDegreeTwoTwelveQuartetEvenKleinNaturalFamily.row85Natural

def data : DegreeTwoTwelveFlexibleProfiles.Data row85Interface :=
  .ofExact rowData (by decide +kernel)
end Row85

namespace Row164
def points : Fin 12 ≃ Fin 12 where
  toFun := ![0, 1, 2, 3, 10, 5, 6, 7, 8, 9, 4, 11]
  invFun := ![0, 1, 2, 3, 10, 5, 6, 7, 8, 9, 4, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lifts : Fin 4 → Model :=
  ![
⟨Multiplicative.ofAdd (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 0, BinaryThreeQuartetLiteralSocles.planeLabel.symm 0, BinaryThreeQuartetLiteralSocles.planeLabel.symm 3] : Vector),
    (Multiplicative.ofAdd 0, Multiplicative.ofAdd 0)⟩,
   ⟨Multiplicative.ofAdd (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 0, BinaryThreeQuartetLiteralSocles.planeLabel.symm 0, BinaryThreeQuartetLiteralSocles.planeLabel.symm 2] : Vector),
    (Multiplicative.ofAdd 0, Multiplicative.ofAdd 0)⟩,
   ⟨Multiplicative.ofAdd (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 0, BinaryThreeQuartetLiteralSocles.planeLabel.symm 2, BinaryThreeQuartetLiteralSocles.planeLabel.symm 1] : Vector),
    (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)⟩,
   ⟨Multiplicative.ofAdd (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 2, BinaryThreeQuartetLiteralSocles.planeLabel.symm 3, BinaryThreeQuartetLiteralSocles.planeLabel.symm 1] : Vector),
    (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)⟩]

theorem bindings (i : Fin 4) : literalAction points (lifts i) = row164Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem original_quotientSocle (N : Subgroup Row164Top) [N.Normal] :
    SocleNormalGeneratorBound (Row164Top ⧸ N) 2 :=
  quotientSocle points lifts row164Generators bindings 2 3 rfl rfl N

def family : row164Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact original_quotientSocle N.1)

def rowData : DegreeTwoTwelveJointFiniteRowData row164Interface 2 1 where
  topSocle := family
  natural := DegreeTwoTwelveRow20NaturalFamily.row164Natural

def data : DegreeTwoTwelveFlexibleProfiles.Data row164Interface :=
  .ofExact rowData (by decide +kernel)
end Row164

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveCubicSquareSocles
end
