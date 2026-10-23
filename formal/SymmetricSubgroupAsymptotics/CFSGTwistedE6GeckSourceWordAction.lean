import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedWeylWords
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceAction
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylWord

/-! Literal original fixed relative words have the same action as the
corresponding canonical matrix words on the SAME E6 tensor image. This
records genuine source witnesses; faithfulness is neither needed nor
asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceWordAction
open CFSGTwistedE6FixedWeylWords CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGTwistedE6FixedWordClassification

def matrixRankOneWord (K : Type) [Field K] (i : Fin 6) : MatrixGroup K :=
  canonicalElementaryRoot rawData K false i 1*canonicalElementaryRoot rawData K true i (-1)*
    canonicalElementaryRoot rawData K false i 1

def matrixWord (K : Type) [Field K] : List (Fin 6)→MatrixGroup K
  | []=>1
  | i::w=>matrixRankOneWord K i*matrixWord K w

theorem matrixWord_val (K : Type) [Field K] (w : List (Fin 6)) :
    (matrixWord K w).val=canonicalWord rawData K w := by
  induction w with
  | nil=>rfl
  | cons i w ih=>
    simp only [matrixWord,Subgroup.coe_mul,ih,canonicalWord]
    rfl

theorem rank_one_action (q : CFSG.PrimePower) (i : Fin 6) :
    imageRepresentation data (q.Extension 2) (rankOneWord q i)=
      matrixAction (q.Extension 2) (matrixRankOneWord (q.Extension 2) i) := by
  simp only [rankOneWord,matrixRankOneWord,map_mul,source_root_action]

theorem word_action (q : CFSG.PrimePower) (w : List (Fin 6)) :
    imageRepresentation data (q.Extension 2) (modelWord q w)=
      matrixAction (q.Extension 2) (matrixWord (q.Extension 2) w) := by
  induction w with
  | nil=>simp only [modelWord,matrixWord,map_one]
  | cons i w ih=>simp only [modelWord,matrixWord,map_mul,rank_one_action,ih]

theorem sourceRelativeWord_action (q : CFSG.PrimePower) (r : List (Fin 4)) :
    imageAction q (sourceRelativeWord q r)=
      matrixAction (q.Extension 2) (matrixWord (q.Extension 2) (expandRelative r)) := by
  change imageRepresentation data (q.Extension 2) (toModel q (sourceRelativeWord q r))=_
  rw [sourceRelativeWord_toModel,word_action]

theorem pairedRoot_action (q : CFSG.PrimePower) (neg : Bool) (j : Fin 2) (t : q.Extension 2) :
    imageAction q (pairedRoot q neg j t)=matrixAction (q.Extension 2)
      (canonicalElementaryRoot rawData (q.Extension 2) neg (pairedNode j) t*
        canonicalElementaryRoot rawData (q.Extension 2) neg
          (CFSG.Models.e6Twist (pairedNode j)) (t^q.order)) := by
  change imageRepresentation data (q.Extension 2) (toModel q (pairedRoot q neg j t))=_
  rw [pairedRoot_toModel,map_mul,source_root_action,source_root_action,map_mul]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSourceWordAction
