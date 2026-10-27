import SymmetricSubgroupAsymptotics.CFSGMonsterSelectedReflectionCentralizerPilot

/-! The SAME six DATA-selected literal reflection words. The root guide
is not a theorem premise. Only square-one, the checked reflection0
membership, and the literal c/d anchors are established here. Other
centralizer memberships and E6 pair relations require their own proofs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords
open CFSG.Models.MonsterConstruction InvolutionBraidTrace CFSGMonsterE8BraidBinding

def conjugator (i : Fin 6) : List (Fin 8) :=
  ![[5,1],[],[],[],[7,5],[7,4,3,2,1]] i

def sourceIndex (i : Fin 6) : Fin 8 := ![0,2,3,6,0,0] i

def word (i : Fin 6) : List (Fin 8) :=
  conjugator i++[sourceIndex i]++(conjugator i).reverse

def reflection (i : Fin 6) : Bimonster := value generator (word i)

 theorem reflection_square (i : Fin 6) : reflection i*reflection i=1 :=
  CFSGMonsterE8BraidBinding.reflection_square (conjugator i) (sourceIndex i)

 theorem word_zero : word 0=CFSGMonsterSelectedReflectionCentralizerPilot.selectedWord := rfl

 theorem zero_mem_centralizer : reflection 0∈nodeCentralizer :=
  CFSGMonsterSelectedReflectionCentralizerPilot.selected_mem_centralizer

 theorem first_anchor : reflection 1=(CFSGMonsterSelectedDerivedInvolution.centralArm 0 : Bimonster) := rfl
 theorem second_anchor : reflection 2=(CFSGMonsterSelectedDerivedInvolution.centralArm 1 : Bimonster) := rfl

end SymmetricSubgroupAsymptotics.CFSGMonsterE6SelectedReflectionWords
