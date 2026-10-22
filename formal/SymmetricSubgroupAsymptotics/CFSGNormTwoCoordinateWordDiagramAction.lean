import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerDiagram
import SymmetricSubgroupAsymptotics.CFSGCartanDiagramLinearAction

/-! The actual integral linear action of a positive-normalizing coordinate
Weyl word is the permutation-linear action of its original Cartan diagram. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordDiagramAction
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoCoordinateNormalizerDiagram
open CFSGCartanDiagramLinearAction
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem normalizer_word_action (K : Type) [Field K] (w : List (Fin r))
    (hn : wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)) :
    ∃σ : Equiv.Perm (Fin r),wordLinear A hs hp b₀ s₀ w=permutationLinear σ ∧
      ∀i j,A (σ i) (σ j)=A i j := by
  obtain ⟨σ,hroot,hA⟩ := normalizer_word_diagram A hd hs hp ho K w hn
  refine ⟨σ,linear_eq_permutation_of_simple_images _ σ ?_,hA⟩
  intro i
  change wordLinear A hs hp b₀ s₀ w (s₀ i:Roots A).val=(coordinateRoot A hd (σ i)).val
  rw [wordLinear_root,hroot i]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordDiagramAction
