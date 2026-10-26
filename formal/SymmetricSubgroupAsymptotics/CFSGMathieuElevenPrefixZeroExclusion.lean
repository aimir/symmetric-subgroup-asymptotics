import SymmetricSubgroupAsymptotics.CFSGMathieuElevenFourTransversalSeedImages

/-! ONE selected prefix (first coordinate0), with720 sparse rejection
witnesses. Each encoded value is11*failedRelator+failedPoint. One moved
point contradicts the corresponding WHOLE relator identity. No other
prefix or accepted-code completeness is asserted by this source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixZeroExclusion
open CFSGMathieuElevenFourTransversalCover CFSGMathieuElevenFourTransversalSeedImages

private def failureCode (j k l : Fin 11) : Fin 55 :=
  match j.val,k.val with
  | 1,2 => (match l.val with | 3 => 24 | 4 => 3 | 5 => 3 | 6 => 3 | 7 => 3 | 8 => 3 | 9 => 24 | _ => 3)
  | 1,3 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 24 | _ => 2)
  | 1,4 => (match l.val with | 3 => 24 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | _ => 2)
  | 1,5 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 24 | 7 => 2 | 8 => 2 | 9 => 2 | _ => 2)
  | 1,6 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | _ => 25)
  | 1,7 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 24 | 9 => 2 | _ => 2)
  | 1,8 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 24 | 9 => 2 | _ => 2)
  | 1,9 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 24 | _ => 2)
  | 1,10 => (match l.val with | 3 => 24 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | _ => 2)
  | 2,2 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 2,3 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 2,4 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 2,5 => (match l.val with | 3 => 23 | 4 => 3 | 5 => 23 | 6 => 23 | 7 => 3 | 8 => 3 | 9 => 23 | _ => 3)
  | 2,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 2,7 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 2,8 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 2,9 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 2,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 3,2 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 23 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 3,3 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 2 | 8 => 1 | 9 => 1 | _ => 1)
  | 3,4 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 2 | 9 => 1 | _ => 1)
  | 3,5 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 23 | _ => 1)
  | 3,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 3,7 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 23)
  | 3,8 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 23 | 9 => 1 | _ => 1)
  | 3,9 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 2 | 9 => 1 | _ => 1)
  | 3,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 2 | 8 => 1 | 9 => 1 | _ => 1)
  | 4,2 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 2)
  | 4,3 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 23 | _ => 1)
  | 4,4 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 23 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 4,5 => (match l.val with | 3 => 1 | 4 => 2 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 4,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 4,7 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 4,8 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 4,9 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 23 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 4,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 23 | _ => 1)
  | 5,2 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 2 | _ => 1)
  | 5,3 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 23 | 9 => 1 | _ => 1)
  | 5,4 => (match l.val with | 3 => 1 | 4 => 23 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 5,5 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 5,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 5,7 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 2 | 8 => 1 | 9 => 1 | _ => 1)
  | 5,8 => (match l.val with | 3 => 1 | 4 => 2 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 5,9 => (match l.val with | 3 => 1 | 4 => 23 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 5,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 23 | 9 => 1 | _ => 1)
  | 6,2 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 2 | _ => 1)
  | 6,3 => (match l.val with | 3 => 1 | 4 => 23 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 6,4 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 6,5 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 6,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 2 | 9 => 1 | _ => 1)
  | 6,7 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 23 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 6,8 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 23 | _ => 1)
  | 6,9 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 23 | 9 => 1 | _ => 1)
  | 6,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 7,2 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 23)
  | 7,3 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 7,4 => (match l.val with | 3 => 1 | 4 => 23 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 7,5 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 7,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 23 | _ => 1)
  | 7,7 => (match l.val with | 3 => 1 | 4 => 2 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 7,8 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 2)
  | 7,9 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 2 | _ => 1)
  | 7,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 23 | 8 => 1 | 9 => 1 | _ => 1)
  | 8,2 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 8,3 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 2 | 9 => 1 | _ => 1)
  | 8,4 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 23 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 8,5 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 2)
  | 8,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 8,7 => (match l.val with | 3 => 1 | 4 => 23 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 8,8 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 23 | 9 => 1 | _ => 1)
  | 8,9 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 2)
  | 8,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 23 | _ => 1)
  | 9,2 => (match l.val with | 3 => 23 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 9,3 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 23 | _ => 1)
  | 9,4 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 2 | 9 => 1 | _ => 1)
  | 9,5 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 2)
  | 9,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 2 | _ => 1)
  | 9,7 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 23 | 8 => 1 | 9 => 1 | _ => 1)
  | 9,8 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 9,9 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 9,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 23 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 10,2 => (match l.val with | 3 => 1 | 4 => 2 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 10,3 => (match l.val with | 3 => 23 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 10,4 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 2 | 9 => 1 | _ => 1)
  | 10,5 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 10,6 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 10,7 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 23 | 9 => 1 | _ => 1)
  | 10,8 => (match l.val with | 3 => 1 | 4 => 23 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 10,9 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 23 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 1)
  | 10,10 => (match l.val with | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | _ => 2)
  | _,_ => 0

def failureRelator (j : Second) (k : Third) (l : Fourth) : Fin 5 :=
  ⟨(failureCode j.val k.val l.val).val/11,by
    have h := (failureCode j.val k.val l.val).isLt
    omega⟩

def failurePoint (j : Second) (k : Third) (l : Fourth) : Fin 11 :=
  ⟨(failureCode j.val k.val l.val).val%11,Nat.mod_lt _ (by decide)⟩

theorem witness_moves : ∀ (j : Second) (k : Third) (l : Fourth),
    relationValue (failureRelator j k l)
      (decodedPermutation ((0,j),(k,l))) ySeed (failurePoint j k l)≠failurePoint j k l := by
  decide +kernel

theorem prefixZero_excluded (j : Second) (k : Third) (l : Fourth) :
    ¬Accepts (decode ((0,j),(k,l))) := by
  intro h
  exact witness_moves j k l
    (accepts_pointwise ((0,j),(k,l)) h (failureRelator j k l) (failurePoint j k l))

theorem excluded_of_first_zero (c : Code) (hc : c.1.1=0) : ¬Accepts (decode c) := by
  rcases c with ⟨⟨i,j⟩,⟨k,l⟩⟩
  change i=0 at hc
  subst i
  exact prefixZero_excluded j k l

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixZeroExclusion
