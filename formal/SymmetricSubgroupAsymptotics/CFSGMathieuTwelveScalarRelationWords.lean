import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePackedPointMaps

/-! Shared scalar evaluator for the SAME seven necessary equations.
Only the typed/packed seed bindings are used. This common template has no
candidate whitelist, numerical capacity, or fixed-prefix hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveScalarRelationWords
open SignedPermutationWordPointEvaluation SignedPermutationWordPointEncoding
open SignedPermutationWordPointEvaluation.Letter
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelveFiveTransversalCover
open CFSGMathieuTwelveRecoveredPairRelations CFSGMathieuTwelveTransversalSeedImages
open CFSGMathieuTwelvePackedPointMaps

def recoverXWord : List Letter := [firstInv,secondInv,firstInv]
def recoverYWord : List Letter := [firstInv,secondInv]

theorem eval_recoverXWord {G : Type*} [Group G] (a u : G) :
    eval a u recoverXWord = recoverX a u := by
  simp only [recoverXWord,eval,value,recoverX,mul_one,mul_assoc]

theorem eval_recoverYWord {G : Type*} [Group G] (a u : G) :
    eval a u recoverYWord = recoverY a u := by
  simp only [recoverYWord,eval,value,recoverY,mul_one]

def relationWordNat (r : ℕ) : List Letter :=
  let v := recoverXWord
  let w := recoverYWord
  match r with
  | 0 => powerWord v 2
  | 1 => powerWord w 3
  | 2 => powerWord (v ++ w) 11
  | 3 => powerWord (inverseWord v ++ inverseWord w ++ v ++ w) 6
  | 4 => powerWord (v ++ w ++ v ++ w ++ v ++ inverseWord w) 6
  | 5 => powerWord (inverseWord v ++ inverseWord (w ++ v ++ w) ++ v ++ (w ++ v ++ w)) 5
  | _ => v ++ w

def relationWord (r : Fin 7) : List Letter := relationWordNat r.val

theorem eval_relationWord {G : Type*} [Group G] (r : Fin 7) (a u : G) :
    eval a u (relationWord r) = relationValue r a u := by
  fin_cases r <;> simp only [relationWord,relationWordNat,eval_power,eval_append,
    eval_inverse,eval_recoverXWord,eval_recoverYWord,relationValue,mul_assoc]

def scalarRelation (r : Fin 7) (c : Code) (p : Fin 12) : Fin 12 :=
  applyWord fixedSeed fixedSeed.symm (decodedPermutation c) (decodedPermutation c).symm
    (relationWord r) p

theorem scalarRelation_eq (r : Fin 7) (c : Code) (p : Fin 12) :
    scalarRelation r c p = (relationValue r firstElement (decode c)).val p := by
  unfold scalarRelation
  simp only [←decode_coe_eq,←firstElement_coe_eq,applyWord_eq,
    eval_relationWord,←relationValue_coe]

def scalarTarget (r : Fin 7) (p : Fin 12) : Fin 12 :=
  if r.val = 6 then fixedSeed p else p

theorem scalarTarget_eq (r : Fin 7) (p : Fin 12) :
    scalarTarget r p = (relationTarget r firstElement).val p := by
  rw [relationTarget_coe,firstElement_coe_eq]
  unfold scalarTarget relationTarget
  split <;> rfl

theorem accepts_scalarRelation (c : Code) (h : Accepts (decode c))
    (r : Fin 7) (p : Fin 12) : scalarRelation r c p = scalarTarget r p := by
  rw [scalarRelation_eq,h r,←scalarTarget_eq]

def packedCandidateForward (i j k l m p : ℕ) : ℕ :=
  packedFirst i (packedSecond j (packedThird k (packedFourth l (packedFifth m p))))

def packedCandidateInverse (i j k l m p : ℕ) : ℕ :=
  packedFifthInverse m (packedFourthInverse l
    (packedThirdInverse k (packedSecondInverse j (packedFirstInverse i p))))

theorem candidateForward_point_eq (c : Code) (p : Fin 12) :
    packedCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val = (decodedPermutation c p).val := by
  dsimp only [packedCandidateForward]
  rw [(fifth_point_eq c.2.2.2.val p).1,
    (fourth_point_eq c.2.2.1.val (fifthSeed c.2.2.2.val p)).1,
    (third_point_eq c.2.1.val (fourthSeed c.2.2.1.val (fifthSeed c.2.2.2.val p))).1,
    (second_point_eq c.1.2.val (thirdSeed c.2.1.val
      (fourthSeed c.2.2.1.val (fifthSeed c.2.2.2.val p)))).1,
    (first_point_eq c.1.1 (secondSeed c.1.2.val (thirdSeed c.2.1.val
      (fourthSeed c.2.2.1.val (fifthSeed c.2.2.2.val p))))).1]
  rfl
theorem candidateInverse_point_eq (c : Code) (p : Fin 12) :
    packedCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val = ((decodedPermutation c).symm p).val := by
  dsimp only [packedCandidateInverse]
  rw [(first_point_eq c.1.1 p).2,
    (second_point_eq c.1.2.val ((firstSeed c.1.1).symm p)).2,
    (third_point_eq c.2.1.val ((secondSeed c.1.2.val).symm ((firstSeed c.1.1).symm p))).2,
    (fourth_point_eq c.2.2.1.val ((thirdSeed c.2.1.val).symm
      ((secondSeed c.1.2.val).symm ((firstSeed c.1.1).symm p)))).2,
    (fifth_point_eq c.2.2.2.val ((fourthSeed c.2.2.1.val).symm ((thirdSeed c.2.1.val).symm
      ((secondSeed c.1.2.val).symm ((firstSeed c.1.1).symm p))))).2]
  rfl
def packedScalarRelation (r i j k l m p : ℕ) : ℕ :=
  applyWord packedFixed packedFixedInverse (packedCandidateForward i j k l m)
    (packedCandidateInverse i j k l m) (relationWordNat r) p

def packedScalarTarget (r p : ℕ) : ℕ := if r = 6 then packedFixed p else p

theorem packedScalarRelation_eq (r : Fin 7) (c : Code) (p : Fin 12) :
    packedScalarRelation r.val c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val = (scalarRelation r c p).val := by
  unfold packedScalarRelation scalarRelation
  exact applyWord_encoding (fun p : Fin 12 => p.val)
    fixedSeed fixedSeed.symm (decodedPermutation c) (decodedPermutation c).symm
    packedFixed packedFixedInverse
    (packedCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val c.2.2.1.val.val c.2.2.2.val.val)
    (packedCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val c.2.2.1.val.val c.2.2.2.val.val)
    (fun p => (fixed_point_eq p).1) (fun p => (fixed_point_eq p).2)
    (candidateForward_point_eq c) (candidateInverse_point_eq c) (relationWord r) p

theorem packedScalarTarget_eq (r : Fin 7) (p : Fin 12) :
    packedScalarTarget r.val p.val = (scalarTarget r p).val := by
  unfold packedScalarTarget scalarTarget
  split
  · exact (fixed_point_eq p).1
  · rfl

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveScalarRelationWords
