import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCandidateReplay
import SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCorrectedReplay

/-! The two frozen replay dictionaries evaluate to the SAME literal
nineteen-root normal form. Equality is proved on roots before applying
selected-root word evaluation; no matrices or fixedness are unfolded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCommonNormalForm
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGNormTwoCoordinateSelectedRootElement
open TwoLetterWordRewrite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem normal_roots_eq :
    CFSGReeFFourInnerBracketCandidateReplay.result.map
        CFSGReeFFourInnerBracketCandidateReplay.root =
      CFSGReeFFourInnerBracketCorrectedReplay.result.map
        CFSGReeFFourInnerBracketCorrectedReplay.root := by
  rfl

theorem normal_values_eq (K : Type) [CommRing K] [CharP K 2] :
    value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho
      CFSGReeFFourInnerBracketCandidateReplay.root K)
      CFSGReeFFourInnerBracketCandidateReplay.result =
    value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho
      CFSGReeFFourInnerBracketCorrectedReplay.root K)
      CFSGReeFFourInnerBracketCorrectedReplay.result := by
  have h := congrArg
    (value (fun k : Roots A => selectedRootElement A hd hs hp ho K k 1)) normal_roots_eq
  simpa only [value,List.map_map,CFSGNormTwoCharTwoRootWordRewrite.parameter,
    Function.comp_def] using h

theorem initial_values_eq (K : Type) [CommRing K] [CharP K 2] :
    value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho
      CFSGReeFFourInnerBracketCandidateReplay.root K)
      CFSGReeFFourInnerBracketCandidateReplay.initial =
    value (CFSGNormTwoCharTwoRootWordRewrite.parameter A hd hs hp ho
      CFSGReeFFourInnerBracketCorrectedReplay.root K)
      CFSGReeFFourInnerBracketCorrectedReplay.initial :=
  (CFSGReeFFourInnerBracketCandidateReplay.collected K).trans
    ((normal_values_eq K).trans (CFSGReeFFourInnerBracketCorrectedReplay.collected K).symm)

end SymmetricSubgroupAsymptotics.CFSGReeFFourInnerBracketCommonNormalForm
