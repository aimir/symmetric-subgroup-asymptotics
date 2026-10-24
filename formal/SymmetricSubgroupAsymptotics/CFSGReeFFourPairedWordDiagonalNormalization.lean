import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordTorus

/-! Actual original Weyl words normalize the proved original diagonal.
The existing torus realization identifies its raw preimage, and the
literal E6 word normalizes that same actual torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPairedWordDiagonalNormalization
open CFSG.Models.Chevalley CFSGFFourOriginalMiddleWords CFSGFFourOriginalBruhatCells
open CFSGFFourOriginalDiagonalTorus CFSGFFourOriginalProductTorus
open CFSGE6GeckProductTorus CFSGFFourE6ProductTorus
open CFSGReeFFourOriginalWeylWords CFSGTwistedE6FixedWordClassification
open CFSGTwistedE6GeckNormalizerEnvelope CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckWeylWordTorus CFSGExceptionalNormTwoBases
open CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalCartanPositiveDefinite
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedWordClassification
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "T" => torusGroup A hs hp E6Base E6Index
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem modelDiagonalPart_eq_rawTorus_comap (K : Type) [_root_.Field K] [Finite K] [CharP K 2] :
    modelDiagonalPart K=(T K).comap (rawHom K) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x,rfl⟩ := exists_model_diagonal_torus K g hg
    change rawHom K (modelProductTorusHom K x)∈T K
    rw [rawHom_modelProductTorus]
    exact rawProductTorus_mem_torus K (torusTuple K x)
  · intro g hg
    exact torus_le_diagonalNormalizer K hg

theorem modelWeylWord_normalizes_diagonal (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (w : List (Fin 4)) :
    modelWeylWord K w∈Subgroup.normalizer (modelDiagonalPart K : Set (Model CartanMatrix.F₄ K)) := by
  rw [modelDiagonalPart_eq_rawTorus_comap]
  have hr : rawHom K (modelWeylWord K w)∈Subgroup.normalizer (T K : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    rw [rawHom_modelWeylWord_relative]
    exact wordUnit_mem_torus_normalizer A hs hp E6Base E6Index K (expandRelative w)
  exact Subgroup.le_normalizer_comap (rawHom K) hr

theorem fixedPairedWord_normalizes_diagonal (m : ℕ) (w : List Bool) :
    fixedPairedWord m w∈Subgroup.normalizer (fixedDiagonal m : Set (originalModelFixed m)) :=
  Subgroup.le_normalizer_comap (originalModelFixed m).subtype
    (modelWeylWord_normalizes_diagonal (Field m) (expandPaired w))

end SymmetricSubgroupAsymptotics.CFSGReeFFourPairedWordDiagonalNormalization
