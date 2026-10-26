import SymmetricSubgroupAsymptotics.SignedPermutationWordPointEvaluation
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPrefixOneOneExclusion

/-! Flattening the SAME five necessary recovered-pair equations, with no
new relation or converse. The checked xSeed and all82 checked transversal
seeds are reused. Inverse candidate maps apply the inverse seeds in the
opposite order, as required by the actual original permutation product. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoScalarRelationWords
open SignedPermutationWordPointEvaluation
open SignedPermutationWordPointEvaluation.Letter
open CFSGMathieuTwentyTwoElevenWords CFSGMathieuTwentyTwoElevenGeneration
open CFSGMathieuTwentyTwoRecoveredPairRelations
open CFSGMathieuTwentyTwoFiveTransversalCover
open CFSGMathieuTwentyTwoTransversalSeedImagesFirst
open CFSGMathieuTwentyTwoTransversalSeedImagesRemaining
open CFSGMathieuTwentyTwoPrefixOneOneExclusion

def recoverAWord : List Letter :=
  [first, first, secondInv, first, secondInv, first, second, first,
    second, second, first, secondInv]

def recoverBWord : List Letter :=
  [first, secondInv, first, second, first, first, first, first, second, first, second]

theorem eval_recoverAWord {G : Type*} [Group G] (v u : G) :
    eval v u recoverAWord = recoverA v u := by
  simp [recoverAWord, eval, value, recoverA, pow_succ, mul_assoc]

theorem eval_recoverBWord {G : Type*} [Group G] (v u : G) :
    eval v u recoverBWord = recoverB v u := by
  simp [recoverBWord, eval, value, recoverB, pow_succ, mul_assoc]

def relationWord (r : Fin 5) : List Letter :=
  match r.val with
  | 0 => powerWord [second] 11
  | 1 => powerWord recoverAWord 5
  | 2 => powerWord recoverBWord 8
  | 3 => powerWord recoverAWord 3 ++ powerWord recoverBWord 2 ++ [firstInv]
  | _ => recoverAWord ++ [Letter.first] ++ inverseWord recoverAWord ++ [secondInv]

theorem eval_relationWord {G : Type*} [Group G] (r : Fin 5) (v u : G) :
    eval v u (relationWord r) = relationValue r v u := by
  fin_cases r <;> simp only [relationWord, eval_power, eval_append, eval_inverse,
    eval_recoverAWord, eval_recoverBWord, eval, value, mul_one, relationValue, mul_assoc]

def candidateForward (c : Code) (p : Fin 22) : Fin 22 :=
  firstSeed c.1.1 (secondSeed c.1.2.val (thirdSeed c.2.1.val
    (fourthSeed c.2.2.1.val (fifthSeed c.2.2.2.val p))))

def candidateInverse (c : Code) (p : Fin 22) : Fin 22 :=
  (fifthSeed c.2.2.2.val).symm ((fourthSeed c.2.2.1.val).symm
    ((thirdSeed c.2.1.val).symm ((secondSeed c.1.2.val).symm ((firstSeed c.1.1).symm p))))

theorem candidateForward_eq (c : Code) : candidateForward c = (decode c).val := by
  rw [decode_coe_eq]
  rfl

theorem candidateInverse_eq (c : Code) :
    candidateInverse c = ((decode c).val).symm := by
  rw [decode_coe_eq]
  rfl

def scalarRelation (r : Fin 5) (c : Code) (p : Fin 22) : Fin 22 :=
  applyWord xSeed xSeed.symm (candidateForward c) (candidateInverse c)
    (relationWord r) p

theorem scalarRelation_eq (r : Fin 5) (c : Code) (p : Fin 22) :
    scalarRelation r c p = (relationValue r firstElement (decode c)).val p := by
  unfold scalarRelation
  simp only [candidateForward_eq, candidateInverse_eq, ← firstElement_coe_eq,
    applyWord_eq, eval_relationWord, ← relationValue_coe]

theorem accepts_scalarRelation (c : Code) (h : Accepts (decode c))
    (r : Fin 5) (p : Fin 22) : scalarRelation r c p = p := by
  rw [scalarRelation_eq, h r]
  rfl

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoScalarRelationWords
