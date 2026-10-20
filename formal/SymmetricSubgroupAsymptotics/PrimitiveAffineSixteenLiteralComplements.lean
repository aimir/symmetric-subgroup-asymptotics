import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenSolubleComplementBindings
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenAllLiteralFrames

/-! The actual point-zero stabilizer in each of the twenty fixed affine16
actions is the corresponding fixed small-affine complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenLiteralComplements
open Non2UnipotentPrefixFiniteMenu

def row1 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup := by
  have hz : PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.affineAction_range

def row2 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearGroup := by
  have hz : PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.linearGroup PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.affineAction_range

def row3 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.affineAction_range

def row4 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow4AffineSocles.affineAction_range

def row5 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.linearGroup := by
  have hz : PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.linearGroup PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.affineAction_range

def row6 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.affineAction_range

def row7 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow7AffineSocles.affineAction_range

def row8 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow8AffineSocles.affineAction_range

def row9 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.affineAction_range

def row10 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow10AffineSocles.affineAction_range

def row11 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.affineAction_range

def row12 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.affineAction_range

def row13 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.affineAction_range

def row14 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.affineAction_range

def row15 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.affineAction_range

def row16 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.affineAction_range

def row17 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.affineAction_range

def row18 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.affineAction_range

def row19 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.affineAction_range

def row20 : MulAction.stabilizer PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.Top (0 : Fin 16) ≃*
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.linearGroup := by
  have hz : BinaryFourAffineImage.pointEquiv 0=0 := by decide +kernel
  rw [←hz]
  exact AffineModel.literalPointStabilizerEquiv PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.linearGroup BinaryFourAffineImage.pointEquiv
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.Top PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.affineAction_range

def complement (i : Fin 20) :
    MulAction.stabilizer
      (PrimitiveAffineSixteenAllLiteralFrames.top ⟨i.val,by omega⟩) (0 : Fin 16) ≃*
      (SmallAffineCanonicalRepresentatives.degreeSixteen i).Carrier := by
  apply Classical.choice
  fin_cases i
  · exact ⟨row1.trans PrimitiveAffineSixteenSolubleComplementBindings.row1⟩
  · exact ⟨row2.trans PrimitiveAffineSixteenSolubleComplementBindings.row2⟩
  · exact ⟨row3.trans PrimitiveAffineSixteenSolubleComplementBindings.row3⟩
  · exact ⟨row4.trans PrimitiveAffineSixteenSolubleComplementBindings.row4⟩
  · exact ⟨row5.trans PrimitiveAffineSixteenSolubleComplementBindings.row5⟩
  · exact ⟨row6.trans PrimitiveAffineSixteenSolubleComplementBindings.row6⟩
  · exact ⟨row7.trans PrimitiveAffineSixteenSolubleComplementBindings.row7⟩
  · exact ⟨row8.trans PrimitiveAffineSixteenSolubleComplementBindings.row8⟩
  · exact ⟨row9.trans PrimitiveAffineSixteenSolubleComplementBindings.row9⟩
  · exact ⟨row10.trans PrimitiveAffineSixteenSolubleComplementBindings.row10⟩
  · exact ⟨row11⟩
  · exact ⟨row12⟩
  · exact ⟨row13⟩
  · exact ⟨row14⟩
  · exact ⟨row15⟩
  · exact ⟨row16⟩
  · exact ⟨row17⟩
  · exact ⟨row18⟩
  · exact ⟨row19⟩
  · exact ⟨row20⟩

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenLiteralComplements
