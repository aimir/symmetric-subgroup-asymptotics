import SymmetricSubgroupAsymptotics.AffineLiteralComplementTransport
import SymmetricSubgroupAsymptotics.SmallAffineCanonicalRepresentatives
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles

/-! Literal displayed linear generators for the first ten affine16 rows
map to the pinned small-affine permutation complement generators. Every
finite equality is pointwise on at most16 points, without enumerating groups. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenSolubleComplementBindings

private theorem first_linearPerm_injective : Function.Injective
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm := by
  intro a b h
  apply LinearEquiv.ext
  intro v
  have he := PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.pointEquiv.permCongrHom.injective h
  exact DFunLike.congr_fun he v

private theorem second_linearPerm_injective : Function.Injective
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearPerm := by
  intro a b h
  apply LinearEquiv.ext
  intro v
  have he := PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.pointEquiv.permCongrHom.injective h
  exact DFunLike.congr_fun he v

def row1 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row1Order.R := by
  have hgen : ∀ j : Fin 1, PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm (PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGenerators j)=SmallAffineSoluble16Row1Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  exact AffineModel.generatedLinearImageEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGenerators PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row1Order.generators hgen

def row2 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row2Order.R := by
  have hgen : ∀ j : Fin 2, PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearPerm (PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearGenerators j)=SmallAffineSoluble16Row2Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  exact AffineModel.generatedLinearImageEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearGenerators PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearPerm
    second_linearPerm_injective SmallAffineSoluble16Row2Order.generators hgen

def row3 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row3Order.R := by
  have hgen : ∀ j : Fin 1, BinaryFourAffineImage.linearPerm ((fun _ : Fin 1 => PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a3) j)=SmallAffineSoluble16Row3Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  have hr : PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.linearGroup=
      Subgroup.closure (Set.range (fun _ : Fin 1 => PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a3)) := by
    rw [Set.range_const,←Subgroup.zpowers_eq_closure]
  rw [hr]
  exact AffineModel.generatedLinearImageEquiv (fun _ : Fin 1 => PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a3) BinaryFourAffineImage.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row3Order.generators hgen

def row4 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row4Order.R := by
  have hgen : ∀ j : Fin 3, BinaryFourAffineImage.linearPerm (PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations.linearGenerators4 j)=SmallAffineSoluble16Row4Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  exact AffineModel.generatedLinearImageEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations.linearGenerators4 BinaryFourAffineImage.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row4Order.generators hgen

def row5 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row5Order.R := by
  have hgen : ∀ j : Fin 2, PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm (PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.linearGenerators j)=SmallAffineSoluble16Row5Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  exact AffineModel.generatedLinearImageEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.linearGenerators PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row5Order.generators hgen

def row6 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row6Order.R := by
  have hgen : ∀ j : Fin 2, BinaryFourAffineImage.linearPerm ((![PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b6, PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a6]) j)=SmallAffineSoluble16Row6Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  change Subgroup.closure ({PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a6,
    PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b6} : Set BinaryFourAffineImage.LinearGroup) ≃* _
  have hr : ({PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a6,
      PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b6} : Set BinaryFourAffineImage.LinearGroup)=
      Set.range (![PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b6, PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a6]) := by simp [Set.pair_comm]
  rw [hr]
  exact AffineModel.generatedLinearImageEquiv (![PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b6, PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a6]) BinaryFourAffineImage.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row6Order.generators hgen

def row7 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row7Order.R := by
  have hgen : ∀ j : Fin 4, BinaryFourAffineImage.linearPerm (PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations.linearGenerators7 j)=SmallAffineSoluble16Row7Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  exact AffineModel.generatedLinearImageEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations.linearGenerators7 BinaryFourAffineImage.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row7Order.generators hgen

def row8 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row8Order.R := by
  have hgen : ∀ j : Fin 3, BinaryFourAffineImage.linearPerm (PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10Complements.linearGenerators8 j)=SmallAffineSoluble16Row8Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  exact AffineModel.generatedLinearImageEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10Complements.linearGenerators8 BinaryFourAffineImage.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row8Order.generators hgen

def row9 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row9Order.R := by
  have hgen : ∀ j : Fin 2, BinaryFourAffineImage.linearPerm ((![PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a9, PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b9]) j)=SmallAffineSoluble16Row9Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  change Subgroup.closure ({PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a9,
    PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b9} : Set BinaryFourAffineImage.LinearGroup) ≃* _
  have hr : ({PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a9,
      PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b9} : Set BinaryFourAffineImage.LinearGroup)=
      Set.range (![PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a9, PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b9]) := by simp [Set.pair_comm]
  rw [hr]
  exact AffineModel.generatedLinearImageEquiv (![PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.a9, PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations.b9]) BinaryFourAffineImage.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row9Order.generators hgen

def row10 : PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.linearGroup ≃*
    SmallAffineSoluble16Row10Order.R := by
  have hgen : ∀ j : Fin 4, BinaryFourAffineImage.linearPerm (PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10Complements.linearGenerators10 j)=SmallAffineSoluble16Row10Order.generators j := by
    intro j
    apply Equiv.ext
    intro x
    revert j x
    decide +kernel
  exact AffineModel.generatedLinearImageEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10Complements.linearGenerators10 BinaryFourAffineImage.linearPerm
    first_linearPerm_injective SmallAffineSoluble16Row10Order.generators hgen

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenSolubleComplementBindings
