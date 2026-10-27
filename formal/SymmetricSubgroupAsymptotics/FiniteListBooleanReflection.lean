import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Basic

/-! Computable list domains and Boolean reflection. Numerical certificates
prove a single Bool equality, rather than constructing a Decidable proof tree
for a finite universal proposition. Completeness and soundness are independent
of any candidate count or group-theoretic capacity. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FiniteListBooleanReflection

def subtypeList {α : Type*} (xs : List α) (p : α → Prop) [DecidablePred p] :
    List {a : α // p a} :=
  xs.filterMap (fun a => if h : p a then some ⟨a,h⟩ else none)

theorem mem_subtypeList {α : Type*} (xs : List α) (p : α → Prop) [DecidablePred p]
    (a : {a : α // p a}) (ha : a.val ∈ xs) : a ∈ subtypeList xs p := by
  apply List.mem_filterMap.mpr
  refine ⟨a.val,ha,?_⟩
  simp only [dif_pos a.property]

theorem all_true_at {α : Type*} (xs : List α) (test : α → Bool)
    (h : xs.all test = true) (a : α) (ha : a ∈ xs) : test a = true :=
  List.all_eq_true.mp h a ha

theorem not_beq_sound {α : Type*} [BEq α] [LawfulBEq α]
    (a b : α) (h : (!(a == b)) = true) : a ≠ b := by
  intro he
  subst b
  simpa using h

end SymmetricSubgroupAsymptotics.FiniteListBooleanReflection
