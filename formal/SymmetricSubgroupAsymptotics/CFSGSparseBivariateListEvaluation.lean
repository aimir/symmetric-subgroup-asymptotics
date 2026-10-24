import SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoListParity
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Fin

/-! Evaluation of explicit exponent lists. Repetition is retained,
so finite parity certificates transport directly to characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGSparseBivariateListEvaluation
variable {K : Type*} [CommSemiring K]

def monomialValue (c d : K) (e : ℕ×ℕ) : K := c^e.1*d^e.2

def evaluate (c d : K) (l : List (ℕ×ℕ)) : K := (l.map (monomialValue c d)).sum

theorem monomialValue_add (c d : K) (p e : ℕ×ℕ) :
    monomialValue c d (p.1+e.1,p.2+e.2)=monomialValue c d p*monomialValue c d e := by
  simp only [monomialValue,pow_add]
  ac_rfl

theorem evaluate_append (c d : K) (l r : List (ℕ×ℕ)) :
    evaluate c d (l++r)=evaluate c d l+evaluate c d r := by
  simp only [evaluate,List.map_append,List.sum_append]

theorem evaluate_shift (c d : K) (p : ℕ×ℕ) (l : List (ℕ×ℕ)) :
    evaluate c d (l.map fun e=>(p.1+e.1,p.2+e.2))=
      monomialValue c d p*evaluate c d l := by
  simp only [evaluate,List.map_map,Function.comp_def,monomialValue_add]
  exact List.sum_map_mul_left _ _ _

theorem evaluate_replicate_flatten (c d : K) (n : ℕ) (l : List (ℕ×ℕ)) :
    evaluate c d (List.replicate n l).flatten=(n : K)*evaluate c d l := by
  induction n with
  | zero => simp only [List.replicate_zero,List.flatten_nil,evaluate,List.map_nil,List.sum_nil,
      Nat.cast_zero,zero_mul]
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons,evaluate_append,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    exact add_comm _ _

theorem evaluate_flatMap {I : Type*} (c d : K) (l : List I) (f : I→List (ℕ×ℕ)) :
    evaluate c d (l.flatMap f)=(l.map fun i=>evaluate c d (f i)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons,evaluate_append,ih]
    rfl

theorem evaluate_eq_of_parity {L : Type*} [CommRing L] [CharP L 2]
    (c d : L) (l r : List (ℕ×ℕ))
    (h : ∀e ∈ l.toFinset∪r.toFinset,l.count e%2=r.count e%2) :
    evaluate c d l=evaluate c d r := by
  apply CFSGCharacteristicTwoListParity.sum_map_eq_of_count_mod_two l r (monomialValue c d)
  simpa only [List.count_eq_countP,beq_eq_decide] using h

end SymmetricSubgroupAsymptotics.CFSGSparseBivariateListEvaluation
