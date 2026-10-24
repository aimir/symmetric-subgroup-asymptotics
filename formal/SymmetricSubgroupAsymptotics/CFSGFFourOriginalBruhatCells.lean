import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalWeylWords
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalAmbientHom
import SymmetricSubgroupAsymptotics.CFSGFFourE6FiniteFixedBruhatCover

/-! Actual U-diagonal-word-U cells in the SAME original F4 Model in
characteristic two, before any projective/simple-group quotient. The
enlarged-envelope block uniqueness likewise transports through the
proved injective original representation; no D=T is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalBruhatCells
open CFSG.Models.Chevalley CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalGeneratedEquivalence CFSGFFourOriginalAmbientHom
open CFSGReeFFourOriginalWeylWords CFSGFFourE6FiniteFixedBruhatCover
open CFSGFFourE6FiniteWeylMenu CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckEnvelopeBlocks CFSGE6GeckFixedPairNormalizer
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6FixedWordClassification
open CFSGNormTwoCoordinateWeylBlocks CFSGExceptionalCartanPositiveDefinite

variable (K : Type) [Field K] [Finite K] [CharP K 2]

def modelEnvelope : Subgroup (Model CartanMatrix.F₄ K) :=
  (normalizerEnvelope K).comap (rawHom K)

def modelDiagonalPart : Subgroup (Model CartanMatrix.F₄ K) :=
  (diagonalNormalizer K).comap (rawHom K)

theorem rawHom_generated_inverse (x : fixedRootGenerated K (RingEquiv.refl K)) :
    rawHom K ((modelEquivGenerated K).symm x)=x.val :=
  (modelEquivGenerated_val K _).symm.trans
    (congrArg (fun y : fixedRootGenerated K (RingEquiv.refl K)=>y.val)
      ((modelEquivGenerated K).apply_symm_apply x))

theorem exists_model_cell (g : Model CartanMatrix.F₄ K) :
    ∃u∈modelPositive K,∃d∈modelDiagonalPart K,∃r : List (Fin 4),
      ∃v∈modelPositive K,g=u*d*modelWeylWord K r*v := by
  let e := modelEquivGenerated K
  obtain ⟨u,hu,d,hdD,i,v,hv,he⟩ := exists_finite_fixed_cell K (RingEquiv.refl K)
    (e g).val (e g).property
  let U : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨u,signedFixed_le_generated K (RingEquiv.refl K) false hu⟩
  let D : fixedRootGenerated K (RingEquiv.refl K) := ⟨d,hdD.2⟩
  let V : fixedRootGenerated K (RingEquiv.refl K) :=
    ⟨v,signedFixed_le_generated K (RingEquiv.refl K) false hv⟩
  have huM : e.symm U∈modelPositive K := by
    change rawHom K (e.symm U)∈Positive K
    rw [rawHom_generated_inverse]
    exact hu.1
  have hvM : e.symm V∈modelPositive K := by
    change rawHom K (e.symm V)∈Positive K
    rw [rawHom_generated_inverse]
    exact hv.1
  have hdM : e.symm D∈modelDiagonalPart K := by
    change rawHom K (e.symm D)∈diagonalNormalizer K
    rw [rawHom_generated_inverse]
    exact pairNormalizer_le_diagonalNormalizer K (RingEquiv.refl K) hdD
  refine ⟨e.symm U,huM,e.symm D,hdM,representative i,e.symm V,hvM,?_⟩
  apply rawHom_injective K
  have hU : rawHom K (e.symm U)=u := rawHom_generated_inverse K U
  have hD : rawHom K (e.symm D)=d := rawHom_generated_inverse K D
  have hV : rawHom K (e.symm V)=v := rawHom_generated_inverse K V
  simp only [map_mul,rawHom_modelWeylWord_relative]
  rw [hU,hD,hV]
  change rawHom K g=u*d*menuMatrix K i*v
  exact (modelEquivGenerated_val K g).symm.trans he

theorem model_cell_word_block_unique (v w : List (Fin 4))
    (b₁ b₂ : Model CartanMatrix.F₄ K) (hb₁ : b₁∈modelEnvelope K) (hb₂ : b₂∈modelEnvelope K)
    (he : b₁*modelWeylWord K v*b₂=modelWeylWord K w) :
    wordBlockPermutation CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (expandRelative v)=
      wordBlockPermutation CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (expandRelative w) := by
  have hraw := congrArg (rawHom K) he
  simp only [map_mul,rawHom_modelWeylWord_relative] at hraw
  exact envelope_bruhat_block_unique K (expandRelative v) (expandRelative w)
    (rawHom K b₁) (rawHom K b₂) hb₁ hb₂ hraw

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalBruhatCells
