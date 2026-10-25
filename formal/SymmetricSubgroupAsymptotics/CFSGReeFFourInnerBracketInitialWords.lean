import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCommonNormalForm
import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketRootWordSemantics

/-! Bind the two frozen replay inputs to their WHOLE constant root words.
The resulting canonical identity retains the actual S/T square correction
and the inner commutator. No individual root membership is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketInitialWords
open CFSGReeFFourInnerBracketRootWordSemantics CFSGReeFFourInnerBracketCommonNormalForm
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGReeFFourMiddleSquareRootWordValues CFSGFFourE6PositiveRootUnits
open CFSGSerreQuadraticWeylWord TwoLetterWordRewrite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def candidateRoots : List (Roots A) :=
  (middleRoots 1).reverse++(middleRoots 0).reverse++
    outerRoots 2++outerRoots 1++outerRoots 0

def correctedRoots : List (Roots A) :=
  outerSquareRoots++squareRoots++yRoots++reflectedRoots++yRoots.reverse++reflectedRoots.reverse

theorem candidate_roots_eq :
    CFSGReeFFourInnerBracketCandidateReplay.initial.map
      CFSGReeFFourInnerBracketCandidateReplay.root = candidateRoots := by
  rfl

theorem corrected_roots_eq :
    CFSGReeFFourInnerBracketCorrectedReplay.initial.map
      CFSGReeFFourInnerBracketCorrectedReplay.root = correctedRoots := by
  rfl

variable (K : Type) [CommRing K] [CharP K 2]

theorem root_values_eq : rootValue K candidateRoots=rootValue K correctedRoots := by
  calc
    _ = rootValue K (CFSGReeFFourInnerBracketCandidateReplay.initial.map
        CFSGReeFFourInnerBracketCandidateReplay.root) :=
      congrArg (rootValue K) candidate_roots_eq.symm
    _ = value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho
        CFSGReeFFourInnerBracketCandidateReplay.root K)
        CFSGReeFFourInnerBracketCandidateReplay.initial := rootValue_map K _ _
    _ = value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho
        CFSGReeFFourInnerBracketCorrectedReplay.root K)
        CFSGReeFFourInnerBracketCorrectedReplay.initial := initial_values_eq K
    _ = rootValue K (CFSGReeFFourInnerBracketCorrectedReplay.initial.map
        CFSGReeFFourInnerBracketCorrectedReplay.root) := (rootValue_map K _ _).symm
    _ = _ := congrArg (rootValue K) corrected_roots_eq

def canonicalCandidate :=
  (CFSGReeFFourInnerBracketFixedBlocks.middleBlock K 1)⁻¹*
    (CFSGReeFFourInnerBracketFixedBlocks.middleBlock K 0)⁻¹*
    CFSGReeFFourInnerBracketFixedBlocks.outerBlock K 2*
    CFSGReeFFourInnerBracketFixedBlocks.outerBlock K 1*
    CFSGReeFFourInnerBracketFixedBlocks.outerBlock K 0

def canonicalCorrected :=
  (MulAut.conj (canonicalWord e6Data K [0,5,1])) (squareWord K)*squareWord K*
    ⁅yWord K,(MulAut.conj (canonicalWord e6Data K [0,5,1])) (yWord K)⁆

theorem candidate_value_eq : rootValue K candidateRoots=canonicalCandidate K := by
  simp only [candidateRoots,rootValue_append,rootValue_reverse,value_outerRoots,
    value_middleRoots,canonicalCandidate]
  rfl

theorem corrected_value_eq : rootValue K correctedRoots=canonicalCorrected K := by
  simp only [correctedRoots,rootValue_append,rootValue_reverse,value_yRoots,
    value_reflectedRoots,value_squareRoots,value_outerSquareRoots,canonicalCorrected,
    commutatorElement_def,mul_assoc]
  rfl

theorem canonical_identity : canonicalCandidate K=canonicalCorrected K :=
  (candidate_value_eq K).symm.trans ((root_values_eq K).trans (corrected_value_eq K))

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketInitialWords
