import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnAction
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalFoldedEquivalence

/-! The selected column certificate concerns literal words in the SAME
original F4 Model. The unconditional parameter-preserving equivalence
transports these words to the proved norm26 action. A single-column
equality is not a whole-word identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylColumnAction
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGFFourOriginalFoldedEquivalence CFSGFFourE6MiddleWeylColumnAction
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6MiddleWeylCoordinateSteps
open CFSGFFourE6CharacteristicTwoNormImage
variable (K : Type) [Field K] [Finite K] [CharP K 2]

def originalLeftWord : Model CartanMatrix.F₄ K :=
  actionWord (fun i : Fin 12=>modelRoot CartanMatrix.F₄ K (leftActions i).1 (leftActions i).2 1)

def originalRightWord : Model CartanMatrix.F₄ K :=
  actionWord (fun i : Fin 56=>modelRoot CartanMatrix.F₄ K (rightActions i).1 (rightActions i).2 1)

private theorem indexed_word_transport {N : ℕ} (letters : Fin N→Bool×Fin 4) :
    modelEquivFolded K
        (actionWord (fun i : Fin N=>modelRoot CartanMatrix.F₄ K (letters i).1 (letters i).2 1))=
      actionWord (fun i : Fin N=>foldedRoot K (letters i).1 (letters i).2 1) := by
  simp only [actionWord,map_list_prod,List.map_reverse,List.map_ofFn]
  apply congrArg (fun f : Fin N→canonicalElementaryGroup CFSGFFourSerreMatrices.realizationData K=>
    (List.ofFn f).reverse.prod)
  funext i
  change modelEquivFolded K (modelRoot CartanMatrix.F₄ K (letters i).1 (letters i).2 1)=
    foldedRoot K (letters i).1 (letters i).2 1
  exact modelEquivFolded_root K (letters i).1 (letters i).2 1

theorem modelEquivFolded_leftWord : modelEquivFolded K (originalLeftWord K)=leftWord K :=
  indexed_word_transport K leftActions

theorem modelEquivFolded_rightWord : modelEquivFolded K (originalRightWord K)=rightWord K :=
  indexed_word_transport K rightActions

theorem selected_original_middle_word_column :
    matrixAction K (modelEquivFolded K (originalLeftWord K))*ᵥ(Pi.single 0 (1:K))=
      matrixAction K (modelEquivFolded K (originalRightWord K))*ᵥ(Pi.single 0 (1:K)) := by
  rw [modelEquivFolded_leftWord,modelEquivFolded_rightWord]
  exact selected_middle_word_column K

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleWeylColumnAction
