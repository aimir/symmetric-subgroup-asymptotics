import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Finite.Card
import Lean.Elab.Tactic.Omega

/-! Positive coefficient blocks admit an elementary finite code. Each
block has one head label and an arbitrary word of interior coefficients.
Flattening marks heads by Sum.inl and interiors by Sum.inr; decoding
recovers the entire ordered list and hence the original multiset.
No matrices or group actions are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteCoefficientMultisetCardinality
variable {A B : Type*}

def weight (m : Multiset (A × List B)) : ℕ :=
  (m.map (fun b => b.2.length+1)).sum

private def flatten : List (A × List B) → List (A ⊕ B)
  | [] => []
  | (a,w)::L => Sum.inl a::(w.map Sum.inr++flatten L)

private def decode : List (A ⊕ B) → List B × List (A × List B)
  | [] => ([],[])
  | Sum.inr b::L => (b::(decode L).1,(decode L).2)
  | Sum.inl a::L => ([],(a,(decode L).1)::(decode L).2)

private theorem decode_inr_append (w : List B) (L : List (A ⊕ B)) :
    decode (w.map Sum.inr++L)=(w++(decode L).1,(decode L).2) := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [List.map_cons,List.cons_append,decode,ih]

private theorem decode_flatten (L : List (A × List B)) :
    decode (flatten L)=([],L) := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    rcases b with ⟨a,w⟩
    simp only [flatten,decode,decode_inr_append,ih,List.append_nil]

private theorem flatten_injective : Function.Injective (flatten (A := A) (B := B)) := by
  intro L M h
  have hh := congrArg (fun w => (decode w).2) h
  simpa only [decode_flatten] using hh

private theorem length_flatten (L : List (A × List B)) :
    (flatten L).length=weight (L : Multiset (A × List B)) := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    rcases b with ⟨a,w⟩
    change (flatten ((a,w)::L)).length=
      weight ((a,w)::ₘ(L : Multiset (A × List B)))
    simp only [flatten,List.length_cons,List.length_append,List.length_map,
      weight,Multiset.map_cons,Multiset.sum_cons] at *
    omega

private theorem exists_code (N : ℕ) (hN : 0 < N)
    (m : Multiset (A × List B)) (hm : weight m=N) :
    ∃ p : A × List.Vector (A ⊕ B) (N-1),
      flatten m.toList=Sum.inl p.1::p.2.val := by
  classical
  have hlen : (flatten m.toList).length=N := by
    rw [length_flatten,Multiset.coe_toList,hm]
  cases hL : m.toList with
  | nil => simp only [hL,flatten,List.length_nil] at hlen; omega
  | cons b L =>
    rcases b with ⟨a,w⟩
    have htail : (w.map Sum.inr++flatten L).length=N-1 := by
      rw [hL,flatten,List.length_cons] at hlen
      omega
    exact ⟨(a,⟨w.map Sum.inr++flatten L,htail⟩),rfl⟩

private def code (N : ℕ) (hN : 0 < N)
    (m : {m : Multiset (A × List B) // weight m=N}) :
    A × List.Vector (A ⊕ B) (N-1) :=
  Classical.choose (exists_code N hN m.val m.property)

private theorem code_spec (N : ℕ) (hN : 0 < N)
    (m : {m : Multiset (A × List B) // weight m=N}) :
    flatten m.val.toList=Sum.inl (code N hN m).1::(code N hN m).2.val :=
  Classical.choose_spec (exists_code N hN m.val m.property)

private theorem code_injective (N : ℕ) (hN : 0 < N) :
    Function.Injective (code (A := A) (B := B) N hN) := by
  intro m n he
  apply Subtype.ext
  have hf : flatten m.val.toList=flatten n.val.toList := by
    rw [code_spec N hN m,code_spec N hN n,he]
  have hh := congrArg (fun L : List (A × List B) => (L : Multiset (A × List B)))
    (flatten_injective hf)
  simpa only [Multiset.coe_toList] using hh

theorem finite_weight [Finite A] [Finite B] (N : ℕ) (hN : 0 < N) :
    Finite {m : Multiset (A × List B) // weight m=N} := by
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  exact Finite.of_injective (code N hN) (code_injective N hN)

theorem card_le [Finite A] [Finite B] (N : ℕ) (hN : 0 < N) :
    Nat.card {m : Multiset (A × List B) // weight m=N} ≤
      Nat.card A*(Nat.card A+Nat.card B)^(N-1) := by
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  calc
    _ ≤ Nat.card (A × List.Vector (A ⊕ B) (N-1)) :=
      Nat.card_le_card_of_injective (code N hN) (code_injective N hN)
    _ = _ := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_prod,card_vector,Fintype.card_sum]

end SymmetricSubgroupAsymptotics.FiniteCoefficientMultisetCardinality
