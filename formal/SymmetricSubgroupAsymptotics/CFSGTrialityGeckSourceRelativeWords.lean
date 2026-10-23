import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFixedSections
import SymmetricSubgroupAsymptotics.CFSGTrialityRelativeWordLanguage

/-! Every relative short/long word has a literal ORIGINAL fixed-group
word with the same action on the common Geck image. This is an explicit
source witness, not an inference from matrix fixedness or faithfulness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceRelativeWords
open CFSGTrialityTripleFixedRoots CFSGTrialityGeckOriginalFixedSections
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckDiagramCovariance
open CFSGTrialityRelativeWordLanguage CFSGSerreFixedRootElements
open CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix

def sourceRelativeWord (q : CFSG.PrimePower) : List Bool → Fixed q
  | [] => 1
  | false::r => CFSGTrialityFixedWeylWords.shortWeyl q * sourceRelativeWord q r
  | true::r => CFSGTrialityFixedWeylWords.longWeyl q * sourceRelativeWord q r

theorem sourceWord_append (K : Type) [Field K] (v w : List (Fin 4)) :
    sourceWord K (v++w) = sourceWord K v*sourceWord K w := by
  induction v with
  | nil => simp only [List.nil_append,sourceWord,one_mul]
  | cons i v ih => rw [List.cons_append,sourceWord,ih,sourceWord,mul_assoc]

theorem sourceRelativeWord_toModel (q : CFSG.PrimePower) (r : List Bool) :
    fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (sourceRelativeWord q r) = sourceWord (q.Extension 3) (expandRelative r) := by
  have hshort : fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (CFSGTrialityFixedWeylWords.shortWeyl q) = sourceWord (q.Extension 3) [0,2,3] := by
    simpa only [sourceWord,sourceRankOneWord,CFSGTrialityFixedWeylWords.rankOneWord,mul_one,mul_assoc]
      using CFSGTrialityFixedWeylWords.shortWeyl_toModel q
  have hlong : fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (CFSGTrialityFixedWeylWords.longWeyl q) = sourceWord (q.Extension 3) [1] := by
    simpa only [sourceWord,sourceRankOneWord,CFSGTrialityFixedWeylWords.rankOneWord,mul_one]
      using CFSGTrialityFixedWeylWords.longWeyl_toModel q
  induction r with
  | nil => exact map_one _
  | cons neg r ih =>
    cases neg
    · change fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
        (fun _ => q.order) (CFSGTrialityFixedWeylWords.shortWeyl q * sourceRelativeWord q r) =
        sourceWord (q.Extension 3) ([0,2,3]++expandRelative r)
      rw [map_mul,hshort,ih,sourceWord_append]
    · change fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
        (fun _ => q.order) (CFSGTrialityFixedWeylWords.longWeyl q * sourceRelativeWord q r) =
        sourceWord (q.Extension 3) ([1]++expandRelative r)
      rw [map_mul,hlong,ih,sourceWord_append]

theorem sourceRelativeWord_action (q : CFSG.PrimePower) (r : List Bool) :
    fixedImageAction q (sourceRelativeWord q r) =
      matrixAction (q.Extension 3) (matrixWord (q.Extension 3) (expandRelative r)) := by
  change imageRepresentation data (q.Extension 3)
    (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (sourceRelativeWord q r)) = _
  rw [sourceRelativeWord_toModel,word_action]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceRelativeWords
