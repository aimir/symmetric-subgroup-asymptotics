import SymmetricSubgroupAsymptotics.CFSGTrialityGeckWeylBlocks
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveTwist
import SymmetricSubgroupAsymptotics.CFSGBlockMonomialBruhatUniqueness
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckArbitraryHeightSupport
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups

/-! Uniqueness of the actual D4 Weyl-root action in a Geck Bruhat cell.
Positive units are strictly triangular for a proved root-separating
integer functional, and the literal torus is diagonal. The generic
invertible block-matrix proof therefore applies to the same matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatBlockUniqueness
open CFSGTrialityD4NormTwo CFSGTrialityD4SeparatingWeight CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckWeylBlocks CFSGTrialityGeckPositiveTwist
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckArbitraryHeightSupport CFSGGradedMatrixSubgroups
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
local instance : LinearOrder WeightBlock := blockOrder

theorem positive_separating_strict (K : Type) [Field K] :
    Positive K ≤ strictUnits
      (weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base separatingHeight) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact canonicalRoot_strict (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index separatingHeight K i t
    (separatingHeight_simple_pos i)

theorem positive_block_triangular (K : Type) [Field K]
    (u : (Matrix GeckIndex GeckIndex K)ˣ) (hu : u ∈ Positive K) :
    (u : Matrix GeckIndex GeckIndex K).BlockTriangular geckBlock := by
  intro i j hij
  change blockHeight (geckBlock j) < blockHeight (geckBlock i) at hij
  rw [blockHeight_geckBlock, blockHeight_geckBlock] at hij
  have hle : weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base separatingHeight i ≤
      weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base separatingHeight j := by omega
  have hne : i ≠ j := by
    intro he
    subst j
    exact lt_irrefl _ hij
  rw [positive_separating_strict K hu i j hle, Matrix.one_apply, if_neg hne]

theorem borel_block_triangular (K : Type) [Field K]
    (b : (Matrix GeckIndex GeckIndex K)ˣ)
    (hb : b ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K) :
    (b : Matrix GeckIndex GeckIndex K).BlockTriangular geckBlock := by
  obtain ⟨u, hu, t, ht, he⟩ := borel_factor (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K b hb
  obtain ⟨d, hd⟩ := torus_diagonal_of_mem (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K t ht
  rw [he, Units.val_mul]
  apply (positive_block_triangular K u hu).mul
  rw [hd]
  exact Matrix.blockTriangular_diagonal _

theorem actual_bruhat_block_unique (K : Type) [Field K]
    (v w : List (Fin 4)) (b₁ b₂ : (Matrix GeckIndex GeckIndex K)ˣ)
    (hb₁ : b₁ ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K)
    (hb₂ : b₂ ∈ borelEnvelope (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K)
    (he : b₁ * wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K v * b₂ =
        wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
          D4_positive_definite Base Index K w) :
    wordBlockPermutation v = wordBlockPermutation w :=
  CFSGBlockMonomialBruhatUniqueness.block_bruhat_permutation_unique geckBlock geckBlock_surjective
    b₁ b₂ _ _ (borel_block_triangular K b₁ hb₁) (borel_block_triangular K b₂ hb₂)
    (wordBlockPermutation v) (wordBlockPermutation w)
    (word_block_support K v) (word_block_support K w) he

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckBruhatBlockUniqueness
