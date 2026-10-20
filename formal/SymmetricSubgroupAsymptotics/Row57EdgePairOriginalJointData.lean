import SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameJointData
import SymmetricSubgroupAsymptotics.AlternatingEdgeTopRecognition
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeBlockNaturalFamily

-- Selected physical receipt; original source SHA256 64959c6bb0c4776f35c34e68bce97840c6cddc553351d12cfc780505c853dbd3.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row57EdgePairOriginalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open AlternatingEdgeOriginalProjectorHeads (Top)

def pointChart : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun z := (![0,3,7,9,5,1,11,4,8,10,6,2] : Fin 12 → Fin 12) ⟨z.1.val+6*z.2.val,by have h:=z.2.val_lt; omega⟩
  invFun := ![(0,0),(5,0),(5,1),(1,0),(1,1),(4,0),(4,1),(2,0),(2,1),(3,0),(3,1),(0,1)]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def code0 : Top := ⟨{
  toFun := ![0,1,2,3]
  invFun := ![0,1,2,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
private def code1 : Top := ⟨{
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
private def code2 : Top := ⟨{
  toFun := ![3,2,1,0]
  invFun := ![3,2,1,0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }, by change Equiv.Perm.sign _=1; decide +kernel⟩
def codes : Fin 3 → Top := ![code0,code1,code2]
def tops : Fin 3 → Equiv.Perm (Fin 6) := fun i => SymmetricFourTwelvePointSocles.edge (codes i).val
private theorem preserves : ∀ i, BinaryPairFrame.Preserves pointChart (row57Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame row57Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators pointChart row57Generators tops preserves
private theorem generator_top (i : Fin 3) :
    pairFrame.top (closureGenerators row57Generators i)=tops i :=
  BinaryPairFrame.ofGenerators_top_generator pointChart row57Generators tops preserves i
private theorem inside : ∀ u : row57Interface.top, ∃ p : Top,
    SymmetricFourTwelvePointSocles.edge p.val=pairFrame.top u := by
  have hr : pairFrame.top.range ≤
      (SymmetricFourTwelvePointSocles.edge.comp (alternatingGroup (Fin 4)).subtype).range := by
    rw [show pairFrame.top.range=Subgroup.closure (Set.range tops) from
      BinaryPairFrame.ofGenerators_top_range pointChart row57Generators tops preserves]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  intro u
  exact hr ⟨u,rfl⟩
private def wa : row57Interface.top := (closureGenerators row57Generators 1)
private def wb : row57Interface.top := (closureGenerators row57Generators 2)*(closureGenerators row57Generators 1)*(closureGenerators row57Generators 2)
private theorem ha : pairFrame.top wa=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.a := by
  simp only [wa,generator_top]
  decide +kernel
private theorem hb : pairFrame.top wb=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.b := by
  let g1 : row57Interface.top := closureGenerators row57Generators 1
  let g2 : row57Interface.top := closureGenerators row57Generators 2
  change pairFrame.top ((g2*g1)*g2) = _
  have h1 : pairFrame.top g1=tops 1 := generator_top 1
  have h2 : pairFrame.top g2=tops 2 := generator_top 2
  calc
    pairFrame.top ((g2*g1)*g2) = pairFrame.top (g2*g1)*pairFrame.top g2 :=
      pairFrame.top.map_mul (g2*g1) g2
    _ = (pairFrame.top g2*pairFrame.top g1)*pairFrame.top g2 :=
      congrArg (fun y => y*pairFrame.top g2) (pairFrame.top.map_mul g2 g1)
    _ = (tops 2*tops 1)*tops 2 := by rw [h1,h2]
    _ = SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.b := by decide +kernel

def topEquiv : Top ≃* pairFrame.top.range :=
  AlternatingEdgeTopRecognition.equiv pairFrame.top inside wa wb ha hb

def flexibleData : DegreeTwoTwelveFlexibleProfiles.Data row57Interface :=
  DegreeTwoTwelveFlexibleProfiles.Data.ofExact
    (AlternatingEdgePairFrameJointData.jointData row57Interface pairFrame topEquiv
      (fun p => AlternatingEdgeTopRecognition.equiv_apply pairFrame.top inside wa wb ha hb p)
      DegreeTwoTwelveThreeBlockNaturalFamily.row57Natural) (by decide +kernel)

end SymmetricSubgroupAsymptotics.Row57EdgePairOriginalJointData
