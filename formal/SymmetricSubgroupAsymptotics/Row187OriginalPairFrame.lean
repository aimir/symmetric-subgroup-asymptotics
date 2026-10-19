import SymmetricSubgroupAsymptotics.AlternatingFourCentralTwoSixImage
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalProjectorHeads
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row187OriginalPairFrame
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open AlternatingFourCentralTwoSixImage (Model action)

def points : Fin 6 × ZMod 2 ≃ Fin 12 where
  toFun x := (#[0,11,4,3,8,7,1,2,9,10,5,6] : Array (Fin 12))[2*x.1.val+x.2.val]!
  invFun x := (#[(0,0),(3,0),(3,1),(1,1),(1,0),(5,0),
    (5,1),(2,1),(2,0),(4,0),(4,1),(0,1)] : Array (Fin 6 × ZMod 2))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def klein : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3,by change Equiv.Perm.sign _=1; decide +kernel⟩
def codes : Fin 3 → Model :=
  ![(1,1),(klein,Multiplicative.ofAdd 1),(AlternatingEdgeOriginalProjectorHeads.a,1)]
def tops : Fin 3 → Equiv.Perm (Fin 6) := fun i => action (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row187Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def frame : BinaryPairFrame row187Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row187Generators tops preserves
def original : Fin 3 → row187Interface.top := closureGenerators row187Generators
private theorem generator_top (i : Fin 3) : frame.top (original i)=tops i :=
  BinaryPairFrame.ofGenerators_top_generator points row187Generators tops preserves i
private def conjugateWord (u v : FiniteGeneratorWord (Fin 3)) : FiniteGeneratorWord (Fin 3) :=
  .mul (.mul u v) (.inv u)
private def cWord : FiniteGeneratorWord (Fin 3) := .generator 2
private def sWord : FiniteGeneratorWord (Fin 3) := .generator 1
private def cSquare : FiniteGeneratorWord (Fin 3) := .mul cWord cWord
def centralWord : FiniteGeneratorWord (Fin 3) :=
  .mul sWord (.mul (conjugateWord cWord sWord) (conjugateWord cSquare sWord))
private def bWord : FiniteGeneratorWord (Fin 3) :=
  .mul (.mul (conjugateWord cWord sWord) centralWord) cWord
def cycleWord : FiniteGeneratorWord (Fin 3) := .mul cWord centralWord

theorem word_top (w : FiniteGeneratorWord (Fin 3)) :
    frame.top (w.eval original)=w.eval tops := by
  have h := w.map_eval frame.top original
  have ht : (fun i => frame.top (original i))=tops := by funext i; exact generator_top i
  rw [ht] at h
  exact h
private theorem a_top : frame.top (cWord.eval original)=
    SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.a := by
  rw [word_top]
  apply Equiv.ext
  decide +kernel
private theorem b_top : frame.top (bWord.eval original)=
    SymmetricFourTwelvePointSocles.edge FourPointAlternatingGeneratorCover.b := by
  rw [word_top]
  apply Equiv.ext
  decide +kernel
private theorem central_top : frame.top (centralWord.eval original)=action (1,Multiplicative.ofAdd 1) := by
  rw [word_top]
  apply Equiv.ext
  decide +kernel
private theorem inside (u : row187Interface.top) : ∃ m : Model,action m=frame.top u := by
  have hr : frame.top.range≤action.range := by
    change (BinaryPairFrame.ofGenerators points row187Generators tops preserves).top.range ≤ action.range
    rw [BinaryPairFrame.ofGenerators_top_range points row187Generators tops preserves]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  exact hr ⟨u,rfl⟩

def topEquiv : Model ≃* frame.top.range :=
  AlternatingFourCentralTwoSixImage.equiv frame.top inside
    (cWord.eval original) (bWord.eval original) (centralWord.eval original) a_top b_top central_top
end SymmetricSubgroupAsymptotics.Row187OriginalPairFrame
