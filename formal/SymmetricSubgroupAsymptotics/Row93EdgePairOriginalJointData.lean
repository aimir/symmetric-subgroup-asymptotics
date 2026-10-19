import SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameJointData
import SymmetricSubgroupAsymptotics.AlternatingEdgeTopRecognition
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairAverageNaturalFamily
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord

-- Selected physical receipt; original source SHA256 64959c6bb0c4776f35c34e68bce97840c6cddc553351d12cfc780505c853dbd3.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row93EdgePairOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open AlternatingEdgeOriginalProjectorHeads (Top)

def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun z := (![0,1,3,9,7,5,11,2,4,10,8,6] : Fin 12 → Fin 12) ⟨z.1.val+6*z.2.val,by have h:=z.2.val_lt; omega⟩
  invFun := ![(0,0),(1,0),(1,1),(2,0),(2,1),(5,0),(5,1),(4,0),(4,1),(3,0),(3,1),(0,1)]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def code0 : Top := ⟨{
  toFun := ![0,1,2,3]
  invFun := ![0,1,2,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
private def code1 : Top := ⟨{
  toFun := ![0,1,2,3]
  invFun := ![0,1,2,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
private def code2 : Top := ⟨{
  toFun := ![3,0,2,1]
  invFun := ![1,3,2,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
private def code3 : Top := ⟨{
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
def codes : Fin 4 → Top := ![code0,code1,code2,code3]
def tops : Fin 4 → Equiv.Perm (Fin 6) := fun i => SymmetricFourTwelvePointSocles.edge (codes i).val
private theorem preserves : ∀ i, BinaryPairFrame.Preserves pointChart (row93Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame row93Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row93Generators tops preserves
private theorem generator_top (i : Fin 4) :
    pairFrame.top (closureGenerators row93Generators i)=tops i :=
  BinaryPairFrame.ofGenerators_top_generator pointChart row93Generators tops preserves i
private theorem inside : ∀ u : row93Interface.top, ∃ p : Top,
    SymmetricFourTwelvePointSocles.edge p.val=pairFrame.top u := by
  have hr : pairFrame.top.range ≤
      (SymmetricFourTwelvePointSocles.edge.comp (alternatingGroup (Fin 4)).subtype).range := by
    rw [show pairFrame.top.range=Subgroup.closure (Set.range tops) from
      BinaryPairFrame.ofGenerators_top_range pointChart row93Generators tops preserves]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  intro u
  exact hr ⟨u,rfl⟩
private def originalAlphabet : Fin 4 → row93Interface.top := closureGenerators row93Generators
private def aWord : FiniteGeneratorWord (Fin 4) := (.mul (.generator 3) (.inv (.generator 2)))
private def bWord : FiniteGeneratorWord (Fin 4) := (.mul (.mul (.generator 2) (.generator 3)) (.generator 2))
private def wa : row93Interface.top := aWord.eval originalAlphabet
private def wb : row93Interface.top := bWord.eval originalAlphabet
private theorem alphabet_top : (fun i => pairFrame.top (originalAlphabet i))=tops :=
  funext generator_top
private theorem ha : pairFrame.top wa=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.a := by
  calc
    pairFrame.top wa = aWord.eval (fun i => pairFrame.top (originalAlphabet i)) :=
      FiniteGeneratorWord.map_eval pairFrame.top originalAlphabet aWord
    _ = aWord.eval tops := congrArg (fun g => aWord.eval g) alphabet_top
    _ = SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.a := by decide +kernel
private theorem hb : pairFrame.top wb=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.b := by
  calc
    pairFrame.top wb = bWord.eval (fun i => pairFrame.top (originalAlphabet i)) :=
      FiniteGeneratorWord.map_eval pairFrame.top originalAlphabet bWord
    _ = bWord.eval tops := congrArg (fun g => bWord.eval g) alphabet_top
    _ = SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.b := by decide +kernel


def topEquiv : Top ≃* pairFrame.top.range :=
  AlternatingEdgeTopRecognition.equiv pairFrame.top inside wa wb ha hb

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row93Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (AlternatingEdgePairFrameJointData.jointData row93Interface pairFrame topEquiv
      (fun p => AlternatingEdgeTopRecognition.equiv_apply pairFrame.top inside wa wb ha hb p)
      PrimitiveAffineDegreeTwoTwelvePairAverageNaturalFamily.row93Natural) (by decide +kernel)

end SymmetricSubgroupAsymptotics.Row93EdgePairOriginalJointData
