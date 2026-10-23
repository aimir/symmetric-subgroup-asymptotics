import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylBlocks
import SymmetricSubgroupAsymptotics.CFSGBlockMonomialBruhatUniqueness
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckArbitraryHeightSupport
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups

/-! A proved positive integral separator gives actual block Bruhat
uniqueness in every coordinate norm-two realization, in every field.
The nontrivial Cartan block is retained throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatBlockUniqueness
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootSeparatingWeight
open CFSGNormTwoCoordinateWeylBlocks CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckArbitraryHeightSupport CFSGGradedMatrixSubgroups
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckBorelFactorization
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "J₀" => GeckIndex A hd hs hp ho
local instance : LinearOrder (WeightBlock A) := blockOrder A

theorem positive_separating_strict (K : Type) [Field K] :
    rootGroup A hs hp b₀ s₀ K false ≤ strictUnits (weight A hs hp b₀ (separatingHeight A)) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  apply canonicalRoot_strict A hs hp b₀ s₀ (separatingHeight A) K i t
  change 0 < separatingHeight A (Pi.single i (1 : ℤ))
  exact separatingHeight_simple_pos A i

theorem positive_block_triangular (K : Type) [Field K]
    (u : (Matrix J₀ J₀ K)ˣ) (hu : u∈rootGroup A hs hp b₀ s₀ K false) :
    (u : Matrix J₀ J₀ K).BlockTriangular (geckBlock A hd hs hp ho) := by
  intro i j hij
  change blockHeight A (geckBlock A hd hs hp ho j) < blockHeight A (geckBlock A hd hs hp ho i) at hij
  rw [blockHeight_geckBlock,blockHeight_geckBlock] at hij
  have hle : weight A hs hp b₀ (separatingHeight A) i ≤
      weight A hs hp b₀ (separatingHeight A) j := by omega
  have hne : i≠j := by intro he;subst j;exact lt_irrefl _ hij
  rw [positive_separating_strict A hd hs hp ho K hu i j hle,Matrix.one_apply,if_neg hne]

theorem borel_block_triangular (K : Type) [Field K]
    (b : (Matrix J₀ J₀ K)ˣ) (hb : b∈borelEnvelope A hs hp b₀ s₀ K) :
    (b : Matrix J₀ J₀ K).BlockTriangular (geckBlock A hd hs hp ho) := by
  obtain ⟨u,hu,t,ht,he⟩ := borel_factor A hs hp b₀ s₀ K b hb
  obtain ⟨d,hdiag⟩ := torus_diagonal_of_mem A hs hp b₀ s₀ K t ht
  rw [he,Units.val_mul]
  apply (positive_block_triangular A hd hs hp ho K u hu).mul
  rw [hdiag]
  exact Matrix.blockTriangular_diagonal _

theorem actual_bruhat_block_unique (hr : 0<r) (K : Type) [Field K]
    (v w : List (Fin r)) (b₁ b₂ : (Matrix J₀ J₀ K)ˣ)
    (hb₁ : b₁∈borelEnvelope A hs hp b₀ s₀ K) (hb₂ : b₂∈borelEnvelope A hs hp b₀ s₀ K)
    (he : b₁*wordUnit A hs hp b₀ s₀ K v*b₂=wordUnit A hs hp b₀ s₀ K w) :
    wordBlockPermutation A hd hs hp ho v=wordBlockPermutation A hd hs hp ho w :=
  CFSGBlockMonomialBruhatUniqueness.block_bruhat_permutation_unique
    (geckBlock A hd hs hp ho) (geckBlock_surjective A hd hs hp ho hr) b₁ b₂ _ _
    (borel_block_triangular A hd hs hp ho K b₁ hb₁) (borel_block_triangular A hd hs hp ho K b₂ hb₂)
    (wordBlockPermutation A hd hs hp ho v) (wordBlockPermutation A hd hs hp ho w)
    (word_block_support A hd hs hp ho K v) (word_block_support A hd hs hp ho K w) he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBruhatBlockUniqueness
