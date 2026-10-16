import SymmetricSubgroupAsymptotics.BinaryThreeQuartetCyclicNineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! Original row166 has actual cyclic-nine linear projection. Its literal
point chart and all four affine offsets are retained; the coprime bound
applies to every original normal quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow166OddSocles
open BinaryThreeQuartetCyclicNineSocles
open PrimitiveAffineDegreeTwoTwelveRow207Socles (Vector)
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open DegreeTwoTwelveJointFiniteRows

def points : Fin 12 ≃ Fin 12 where
  toFun := ![3, 7, 11, 0, 1, 8, 9, 4, 5, 6, 10, 2]
  invFun := ![3, 4, 11, 0, 7, 8, 9, 1, 5, 6, 10, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lifts : Fin 4 → Model :=
  ![⟨Multiplicative.ofAdd
        (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 0,
          BinaryThreeQuartetLiteralSocles.planeLabel.symm 0,
          BinaryThreeQuartetLiteralSocles.planeLabel.symm 3] : Vector),
        Multiplicative.ofAdd 0⟩,
    ⟨Multiplicative.ofAdd
        (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 0,
          BinaryThreeQuartetLiteralSocles.planeLabel.symm 0,
          BinaryThreeQuartetLiteralSocles.planeLabel.symm 2] : Vector),
        Multiplicative.ofAdd 0⟩,
    ⟨Multiplicative.ofAdd
        (![BinaryThreeQuartetLiteralSocles.planeLabel.symm 3,
          BinaryThreeQuartetLiteralSocles.planeLabel.symm 3,
          BinaryThreeQuartetLiteralSocles.planeLabel.symm 3] : Vector),
        Multiplicative.ofAdd 6⟩,
    ⟨Multiplicative.ofAdd (0 : Vector), Multiplicative.ofAdd 1⟩]

theorem bindings (i : Fin 4) : literalAction points (lifts i) = row166Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem original_quotientSocle (N : Subgroup Row166Top) [N.Normal] :
    SocleNormalGeneratorBound (Row166Top ⧸ N) 1 :=
  quotientSocle points lifts row166Generators bindings 3 rfl N

def family : row166Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact original_quotientSocle N.1)

def rowData : DegreeTwoTwelveJointFiniteRowData row166Interface 1 1 where
  topSocle := family
  natural := PrimitiveAffineDegreeTwoTwelveTwistedAlternatingNaturalFamily.row166Natural

def data : DegreeTwoTwelveFlexibleProfiles.Data row166Interface :=
  .ofExact rowData (by decide +kernel)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow166OddSocles

end
