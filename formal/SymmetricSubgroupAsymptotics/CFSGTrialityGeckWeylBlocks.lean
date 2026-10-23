import SymmetricSubgroupAsymptotics.CFSGTrialityD4SeparatingWeight
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDiagramCovariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import Mathlib.Logic.Equiv.Option

/-! Actual Geck Weyl words are invertible block permutations of the
twenty-four root lines and the single Cartan block. The lattice support
theorem supplies this assertion in every coefficient characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckWeylBlocks
open CFSGTrialityD4NormTwo CFSGTrialityD4SeparatingWeight CFSGTrialityGeckDiagramCovariance
open CFSGNormTwoRootPairing CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWordLatticeSupport

def geckBlock : GeckIndex → WeightBlock
  | Sum.inl _ => none
  | Sum.inr k => some k

theorem geckBlock_surjective : Function.Surjective geckBlock := by
  intro a
  cases a with
  | none => exact ⟨Sum.inl (Index 0), rfl⟩
  | some k => exact ⟨Sum.inr k, rfl⟩

theorem blockVector_geckBlock (i : GeckIndex) :
    blockVector (geckBlock i) =
      latticeWeight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base i := by
  cases i <;> rfl

theorem blockHeight_geckBlock (i : GeckIndex) :
    blockHeight (geckBlock i) =
      -weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
        Base separatingHeight i := by
  cases i <;> rfl

def rootWordPermutation : List (Fin 4) → Equiv.Perm (Roots (CartanMatrix.D 4))
  | [] => Equiv.refl _
  | i :: w => (rootWordPermutation w).trans
      ((rootPairing (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite).reflectionPerm (Index i))

theorem rootWordPermutation_apply (w : List (Fin 4)) (k : Roots (CartanMatrix.D 4)) :
    rootWordPermutation w k = wordRoot (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index w k := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (rootPairing (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite).reflectionPerm (Index i) (rootWordPermutation w k) = _
    rw [ih]
    rfl

def wordBlockPermutation (w : List (Fin 4)) : Equiv.Perm WeightBlock :=
  Equiv.optionCongr (rootWordPermutation w)

theorem blockVector_wordBlockPermutation (w : List (Fin 4)) (a : WeightBlock) :
    blockVector (wordBlockPermutation w a) =
      wordLinear (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index w (blockVector a) := by
  cases a with
  | none =>
    change (0 : Fin 4 → ℤ) = wordLinear (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index w 0
    exact (map_zero _).symm
  | some k =>
    change (rootWordPermutation w k).val = wordLinear (CartanMatrix.D 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite Base Index w k.val
    rw [rootWordPermutation_apply]
    exact (wordLinear_root (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index w k).symm

theorem word_block_support (K : Type) [Field K] (w : List (Fin 4))
    (i j : GeckIndex) (hij : geckBlock i ≠ wordBlockPermutation w (geckBlock j)) :
    (wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w : Matrix GeckIndex GeckIndex K) i j = 0 := by
  apply word_lattice_support (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K w i j
  intro he
  apply hij
  apply blockVector_injective
  rw [blockVector_geckBlock, blockVector_wordBlockPermutation, blockVector_geckBlock]
  exact he

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckWeylBlocks
