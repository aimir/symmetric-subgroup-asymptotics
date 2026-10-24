import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerEnvelope

/-! Equal actual integral Weyl actions leave a residual in the simultaneous
positive/opposite normalizer. The proof uses the literal inverse word and
identity-word root-line normalization; it does not identify that residual
with a torus or discard its original matrix value. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEqualWordNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinateRootLineNormalizers CFSGNormTwoCoordinateNormalizerEnvelope
open CFSGNormTwoCoordinateNormalizerSoluble
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem equal_action_word_quotient_mem_diagonalNormalizer (K : Type) [Field K]
    (v w : List (Fin r))
    (he : wordLinear A hs hp b₀ s₀ v=wordLinear A hs hp b₀ s₀ w) :
    wordUnit A hs hp b₀ s₀ K v*(wordUnit A hs hp b₀ s₀ K w)⁻¹∈
      diagonalNormalizer A hd hs hp ho K := by
  let n := v++inverseWord w
  have hn : wordLinear A hs hp b₀ s₀ n=1 := by
    rw [show n=v++inverseWord w from rfl,wordLinear_append,wordLinear_inverseWord,he,mul_inv_cancel]
  have hvalue : wordUnit A hs hp b₀ s₀ K n=
      wordUnit A hs hp b₀ s₀ K v*(wordUnit A hs hp b₀ s₀ K w)⁻¹ := by
    rw [show n=v++inverseWord w from rfl,wordUnit_append,wordUnit_inverseWord]
  rw [←hvalue]
  refine ⟨⟨?_,?_⟩,wordUnit_mem_canonical A hd hs hp ho K n⟩
  · rw [word_eq_canonicalWord]
    exact identity_word_normalizes A hd hs hp ho K n hn false
  · rw [word_eq_canonicalWord]
    exact identity_word_normalizes A hd hs hp ho K n hn true

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEqualWordNormalizer
