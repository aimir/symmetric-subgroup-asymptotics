import SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameJointData
import SymmetricSubgroupAsymptotics.AlternatingEdgeTopRecognition
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord

-- Selected physical receipt; original source SHA256 b3d51c779c0a32d712ef19cb0085689db28b629858df3bda1d8419af77cb488e.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row144EdgePairOriginalJointData
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
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
private def code2 : Top := ⟨{
  toFun := ![3,0,2,1]
  invFun := ![1,3,2,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
def codes : Fin 3 → Top := ![code0,code1,code2]
def tops : Fin 3 → Equiv.Perm (Fin 6) := fun i => SymmetricFourTwelvePointSocles.edge (codes i).val
private theorem preserves : ∀ i, BinaryPairFrame.Preserves pointChart (row144Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame row144Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row144Generators tops preserves
private theorem generator_top (i : Fin 3) :
    pairFrame.top (closureGenerators row144Generators i)=tops i :=
  BinaryPairFrame.ofGenerators_top_generator pointChart row144Generators tops preserves i
private theorem inside : ∀ u : row144Interface.top, ∃ p : Top,
    SymmetricFourTwelvePointSocles.edge p.val=pairFrame.top u := by
  have hr : pairFrame.top.range ≤
      (SymmetricFourTwelvePointSocles.edge.comp (alternatingGroup (Fin 4)).subtype).range := by
    rw [show pairFrame.top.range=Subgroup.closure (Set.range tops) from
      BinaryPairFrame.ofGenerators_top_range pointChart row144Generators tops preserves]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  intro u
  exact hr ⟨u,rfl⟩
private def originalAlphabet : Fin 3 → row144Interface.top := closureGenerators row144Generators
private def aWord : FiniteGeneratorWord (Fin 3) := (.mul (.generator 1) (.inv (.generator 2)))
private def bWord : FiniteGeneratorWord (Fin 3) := (.mul (.mul (.generator 1) (.inv (.generator 2))) (.generator 1))
private def wa : row144Interface.top := aWord.eval originalAlphabet
private def wb : row144Interface.top := bWord.eval originalAlphabet
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

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row144Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (AlternatingEdgePairFrameJointData.jointData row144Interface pairFrame topEquiv
      (fun p => AlternatingEdgeTopRecognition.equiv_apply pairFrame.top inside wa wb ha hb p)
      DegreeTwoTwelveThreeBlockNaturalFamily.row144Natural) (by decide +kernel)

end SymmetricSubgroupAsymptotics.Row144EdgePairOriginalJointData
