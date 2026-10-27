import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Abstract sequential trajectories for literal positive operator words.
All composition/reversal algebra is proved with operators and vectors
abstract, so a concrete certificate never converts a long raw-matrix
composition applied to a literal vector. No operator order is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.ListPositiveWordTrajectory

variable {B V : Type*}

def run (f : B → V → V) : List B → V → V
  | [],v => v
  | s::tail,v => run f tail (f s v)

theorem run_append (f : B → V → V) (s t : List B) (v : V) :
    run f (s++t) v=run f t (run f s v) := by
  induction s generalizing v with
  | nil => rfl
  | cons a s ih => exact ih (f a v)

/-- Every transition has a literal intermediate vector; no composed
operator is evaluated in the finite certificate. -/
inductive Steps (f : B → V → V) : List B → V → V → Prop
  | nil (v : V) : Steps f [] v v
  | cons {s : B} {tail : List B} {v v' w : V}
      (first : f s v=v') (rest : Steps f tail v' w) : Steps f (s::tail) v w

theorem run_eq_of_steps {f : B → V → V} {word : List B} {v w : V}
    (h : Steps f word v w) : run f word v=w := by
  induction h with
  | nil v => rfl
  | @cons s tail v v' w first rest ih =>
    change run f tail (f s v)=w
    rw [first]
    exact ih

variable {R : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

theorem prod_apply_eq_run_reverse (E : B → Module.End R V) (word : List B) (v : V) :
    (word.map E).prod v=run (fun s z => E s z) word.reverse v := by
  induction word with
  | nil => rfl
  | cons s tail ih =>
    rw [List.reverse_cons,run_append]
    change E s ((tail.map E).prod v)=E s (run (fun b z => E b z) tail.reverse v)
    exact congrArg (E s) ih

/-- The rightmost letter acts first. This is the only word-to-sequence
conversion needed by concrete positive-word certificates. -/
theorem prod_apply_eq_of_steps (E : B → Module.End R V) (word : List B) (v w : V)
    (h : Steps (fun s z => E s z) word.reverse v w) : (word.map E).prod v=w :=
  (prod_apply_eq_run_reverse E word v).trans (run_eq_of_steps h)

end SymmetricSubgroupAsymptotics.ListPositiveWordTrajectory
