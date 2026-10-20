import SymmetricSubgroupAsymptotics.SymmetricFourTwelvePointSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveOppositePairNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! The original row9 action is the edge/sign action of the literal `S₄`.
Three point bindings identify its entire original generating tuple. The
normal-chain proof handles every original quotient simultaneously; no normal
subgroup census is used. Its checked opposite-pair natural capacity is two. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricEdgeSignSocles

open SymmetricFourTwelvePointSocles
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

def labels : Fin 12 ≃ Fin 12 where
  toFun := ![1, 4, 9, 0, 11, 2, 5, 8, 3, 6, 7, 10]
  invFun := ![3, 0, 5, 8, 1, 6, 9, 10, 7, 2, 11, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def points : Point ≃ Fin 12 := (finProdFinEquiv : Point ≃ Fin 12).trans labels

theorem bindings (i : Fin 3) : literalAction points (generators i) = row9Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem original_quotientSocle (N : Subgroup Row9Top) [N.Normal] :
    SocleNormalGeneratorBound (Row9Top ⧸ N) 1 :=
  quotientSocle points generators row9Generators generates bindings N

def family : row9Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact original_quotientSocle N.1)

def rowData : DegreeTwoTwelveJointFiniteRowData row9Interface 1 2 where
  topSocle := family
  natural := PrimitiveAffineDegreeTwoTwelveOppositePairNaturalFamily.row9Natural

def data : DegreeTwoTwelveFlexibleProfiles.Data row9Interface :=
  .ofExact rowData (by decide +kernel)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricEdgeSignSocles

end
