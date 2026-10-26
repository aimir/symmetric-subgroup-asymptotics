import SymmetricSubgroupAsymptotics.CFSGMathieuElevenAcceptedCodes

/-! Natural prefix1: each of720 codes is either in the shared
eight-code whitelist or has a sparse failed-relator/point witness.
Whitelisted codes need no positive relation check for this upper bound.
No proof/resource setting is raised. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixOneCapacity
open CFSGMathieuElevenFourTransversalCover CFSGMathieuElevenFourTransversalSeedImages CFSGMathieuElevenAcceptedCodes

private def failureCode (j k l : Fin 11) : Fin 55 :=
  match j.val,k.val with
  | 1,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 1,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 1,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 1,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 1,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 1,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 1,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 1,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 1,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 2,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 3,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 4,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 5,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 6,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 7,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 8,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,2 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,3 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,4 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,5 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,6 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,7 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,8 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,9 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 9,10 => (match l.val with | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0 | 8 => 0 | 9 => 0 | _ => 0)
  | 10,2 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 22 | _ => 2)
  | 10,3 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 22 | 9 => 2 | _ => 2)
  | 10,4 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 22 | 9 => 2 | _ => 2)
  | 10,5 => (match l.val with | 3 => 3 | 4 => 22 | 5 => 22 | 6 => 22 | 7 => 22 | 8 => 3 | 9 => 3 | _ => 3)
  | 10,6 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | _ => 22)
  | 10,7 => (match l.val with | 3 => 22 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | _ => 2)
  | 10,8 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | _ => 22)
  | 10,9 => (match l.val with | 3 => 22 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | _ => 2)
  | 10,10 => (match l.val with | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 22 | 9 => 2 | _ => 2)
  | _,_ => 0

def failureRelator (j : Second) (k : Third) (l : Fourth) : Fin 5 :=
  ⟨(failureCode j.val k.val l.val).val/11,by
    have h := (failureCode j.val k.val l.val).isLt
    omega⟩

def failurePoint (j : Second) (k : Third) (l : Fourth) : Fin 11 :=
  ⟨(failureCode j.val k.val l.val).val%11,Nat.mod_lt _ (by decide)⟩

theorem witness_certificate : ∀ (j : Second) (k : Third) (l : Fourth),
    ((1,j),(k,l))∈acceptedCodes ∨
    relationValue (failureRelator j k l)
      (decodedPermutation ((1,j),(k,l))) ySeed (failurePoint j k l)≠failurePoint j k l := by
  decide +kernel

theorem prefix_complete (j : Second) (k : Third) (l : Fourth)
    (h : Accepts (decode ((1,j),(k,l)))) : ((1,j),(k,l))∈acceptedCodes := by
  rcases witness_certificate j k l with hmem|hmove
  · exact hmem
  · exact (hmove (accepts_pointwise ((1,j),(k,l)) h
      (failureRelator j k l) (failurePoint j k l))).elim

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenPrefixOneCapacity
