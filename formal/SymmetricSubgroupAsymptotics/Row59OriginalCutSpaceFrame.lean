import SymmetricSubgroupAsymptotics.AlternatingEdgePairFrameKernel
import SymmetricSubgroupAsymptotics.AlternatingEdgeTopRecognition
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row59OriginalCutSpaceFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open AlternatingEdgeOriginalProjectorHeads (Top a t)

def points : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun x := (#[1,2,5,6,9,10,3,4,11,0,7,8] : Array (Fin 12))[2*x.1.val+x.2.val]!
  invFun x := (#[(4,1),(0,0),(0,1),(3,0),(3,1),(1,0),
    (1,1),(5,0),(5,1),(2,0),(2,1),(4,0)] : Array (Fin 6 × ZMod 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def codes : Fin 4 → Top := ![1,1,t 1,a]
def tops : Fin 4 → Equiv.Perm (Fin 6) := fun i => SymmetricFourTwelvePointSocles.edge (codes i).val
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row59Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def frame : BinaryPairFrame row59Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row59Generators tops preserves

def original : Fin 4 → row59Interface.top := closureGenerators row59Generators
private theorem generator_top (i : Fin 4) : frame.top (original i)=tops i :=
  BinaryPairFrame.ofGenerators_top_generator points row59Generators tops preserves i
private def edgeTop : Top →* Equiv.Perm (Fin 6) :=
  SymmetricFourTwelvePointSocles.edge.comp (alternatingGroup (Fin 4)).subtype
private theorem range_le : frame.top.range≤edgeTop.range := by
  rw [show frame.top.range=Subgroup.closure (Set.range tops) from
    BinaryPairFrame.ofGenerators_top_range points row59Generators tops preserves]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨codes i,rfl⟩
private theorem inside (u : row59Interface.top) :
    ∃ p : Top,SymmetricFourTwelvePointSocles.edge p.val=frame.top u :=
  range_le ⟨u,rfl⟩
private theorem wa : frame.top (original 3)=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.a :=
  generator_top 3
private theorem wb : frame.top (original 2*original 3)=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.b := by
  calc
    _=frame.top (original 2)*frame.top (original 3) := frame.top.map_mul _ _
    _=tops 2*tops 3 := congrArg₂ (fun x y : Equiv.Perm (Fin 6) => x*y) (generator_top 2) (generator_top 3)
    _=SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.b := by decide +kernel

def topEquiv : Top ≃* frame.top.range :=
  AlternatingEdgeTopRecognition.equiv frame.top inside (original 3) (original 2*original 3) wa wb
private theorem topEquiv_apply (p : Top) :
    (topEquiv p).val=SymmetricFourTwelvePointSocles.edge p.val := rfl

def top : row59Interface.top →* Top := AlternatingEdgePairFrameKernel.top frame topEquiv
abbrev kernelModule := AlternatingEdgePairFrameKernel.kernelModule frame topEquiv
def originalKernelChart : OriginalKernelModuleChart top kernelModule :=
  AlternatingEdgePairFrameKernel.originalKernelChart frame topEquiv

def inclusion := AlternatingEdgePairFrameKernel.inclusion frame topEquiv topEquiv_apply

theorem inclusion_injective : Function.Injective inclusion :=
  AlternatingEdgePairFrameKernel.inclusion_injective frame topEquiv topEquiv_apply
end SymmetricSubgroupAsymptotics.Row59OriginalCutSpaceFrame
