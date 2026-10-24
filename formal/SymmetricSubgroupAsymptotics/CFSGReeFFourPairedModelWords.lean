import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedWordClassification
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeSimpleWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateEqualWordNormalizer

/-! Paired words retain their actual original Model values and are
exceptional-fixed. Equal lattice actions of two original words leave
an actual original simultaneous-normalizer residual, rather than an
asserted equality of group words or an asserted torus identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPairedModelWords
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourOriginalWeylWords
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourPairedWordActions
open CFSGReeFFourFixedWordClassification CFSGFFourOriginalMiddleWords
open CFSGFFourOriginalBruhatCells CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification CFSGNormTwoCoordinateEqualWordNormalizer
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem modelWeylWord_append (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (v w : List (Fin 4)) :
    modelWeylWord K (v++w)=modelWeylWord K v*modelWeylWord K w := by
  induction v with
  | nil=>simp only [List.nil_append,modelWeylWord,one_mul]
  | cons i v ih=>rw [List.cons_append,modelWeylWord,ih,modelWeylWord,mul_assoc]

theorem paired_model_word_fixed (m : ℕ) (s : List Bool) :
    reeAutomorphism m (modelWeylWord (Field m) (expandPaired s))=
      modelWeylWord (Field m) (expandPaired s) := by
  have hsingle (b : Bool) :
      reeAutomorphism m (modelWeylWord (Field m) (pairedRelativeWord b))=
        modelWeylWord (Field m) (pairedRelativeWord b) := by
    cases b
    · simpa only [pairedRelativeWord,Bool.false_eq_true,ite_false,modelWeylWord,mul_one,
        outerRelativeWeyl] using outerRelativeWeyl_fixed m
    · simpa only [pairedRelativeWord,ite_true,modelWeylWord,mul_one,mul_assoc,
        middleRelativeWeyl] using middleRelativeWeyl_fixed m
  induction s with
  | nil=>exact map_one (reeAutomorphism m)
  | cons b s ih=>simp only [expandPaired,modelWeylWord_append,map_mul,hsingle,ih]

theorem equal_action_model_residual_mem (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (v w : List (Fin 4))
    (he : linearAction (expandRelative v)=linearAction (expandRelative w)) :
    modelWeylWord K v*(modelWeylWord K w)⁻¹∈modelDiagonalPart K := by
  change rawHom K (modelWeylWord K v*(modelWeylWord K w)⁻¹)∈
    CFSGTwistedE6GeckNormalizerEnvelope.diagonalNormalizer K
  simp only [map_mul,map_inv,rawHom_modelWeylWord_relative]
  exact equal_action_word_quotient_mem_diagonalNormalizer A hd hs hp ho K
    (expandRelative v) (expandRelative w) he

end SymmetricSubgroupAsymptotics.CFSGReeFFourPairedModelWords
