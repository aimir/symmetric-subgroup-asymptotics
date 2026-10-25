import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.SplitIfs

/-! A syntactic two-letter word-rewrite checker and its actual monoid
semantics. The checker validates positions and source letters. Each local
rule must separately have its proved semantic equality; the checker never
assumes a normal-form theorem or a group recognition result. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.TwoLetterWordRewrite

inductive Rule (I : Type*) where
  | cancel (a : I)
  | swap (a b : I)
  | raise (a b c : I)
  deriving DecidableEq

namespace Rule

def before {I : Type*} : Rule I → List I
  | .cancel a => [a,a]
  | .swap a b => [a,b]
  | .raise a b _ => [a,b]

def after {I : Type*} : Rule I → List I
  | .cancel _ => []
  | .swap a b => [b,a]
  | .raise a b c => [c,b,a]

end Rule

structure Step (I : Type*) where
  position : ℕ
  rule : Rule I
  deriving DecidableEq

def value {I G : Type*} [Monoid G] (f : I → G) (w : List I) : G := (w.map f).prod

private theorem value_append {I G : Type*} [Monoid G] (f : I → G) (a b : List I) :
    value f (a++b) = value f a*value f b := by
  simp only [value,List.map_append,List.prod_append]

def applyStep {I : Type*} [DecidableEq I] (s : Step I) (w : List I) : Option (List I) :=
  match w.drop s.position with
  | a::b::tail =>
    if [a,b] = s.rule.before then some (w.take s.position++s.rule.after++tail) else none
  | _ => none

def run {I : Type*} [DecidableEq I] : List (Step I) → List I → Option (List I)
  | [],w => some w
  | s::ss,w => (applyStep s w).bind (run ss)

theorem applyStep_sound {I G : Type*} [DecidableEq I] [Monoid G]
    (f : I → G) (s : Step I) (w w' : List I)
    (hrule : value f s.rule.before = value f s.rule.after)
    (h : applyStep s w = some w') : value f w = value f w' := by
  cases hd : w.drop s.position with
  | nil =>
    simp only [applyStep,hd] at h
    cases h
  | cons a tail =>
    cases tail with
    | nil =>
      simp only [applyStep,hd] at h
      cases h
    | cons b tail =>
      simp only [applyStep,hd] at h
      split_ifs at h with hp
      · have hh := Option.some.inj h
        have hw : w = w.take s.position++[a,b]++tail := by
          calc
            w = w.take s.position++w.drop s.position := (List.take_append_drop _ _).symm
            _ = _ := by simp only [hd,List.append_assoc,List.cons_append,List.nil_append]
        have hl : value f [a,b] = value f s.rule.after :=
          (congrArg (value f) hp).trans hrule
        calc
          _ = value f (w.take s.position++[a,b]++tail) := congrArg (value f) hw
          _ = value f (w.take s.position++s.rule.after++tail) := by
            rw [value_append,value_append,value_append,value_append,hl]
          _ = _ := congrArg (value f) hh

theorem run_sound {I G : Type*} [DecidableEq I] [Monoid G]
    (f : I → G) (steps : List (Step I)) (w w' : List I)
    (hrules : ∀ s ∈ steps, value f s.rule.before = value f s.rule.after)
    (h : run steps w = some w') : value f w = value f w' := by
  induction steps generalizing w w' with
  | nil =>
    simp only [run,Option.some.injEq] at h
    exact congrArg (value f) h
  | cons s ss ih =>
    cases hs : applyStep s w with
    | none =>
      simp only [run,hs,Option.bind] at h
      cases h
    | some v =>
      have ht : run ss v = some w' := by simpa only [run,hs,Option.bind] using h
      exact (applyStep_sound f s w v (hrules s (by simp)) hs).trans
        (ih v w' (fun t ht => hrules t (List.mem_cons_of_mem s ht)) ht)

end SymmetricSubgroupAsymptotics.TwoLetterWordRewrite
