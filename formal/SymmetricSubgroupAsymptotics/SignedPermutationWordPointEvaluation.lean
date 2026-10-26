import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.Basic

/-! Scalar evaluation of signed words. The list records an ordinary product:
its rightmost letter acts first. No finiteness, group-order or capacity
hypothesis is used. Forward and inverse point maps remain separate inputs. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SignedPermutationWordPointEvaluation

inductive Letter where
  | first | firstInv | second | secondInv
  deriving DecidableEq, Repr

open Letter

def inverseLetter : Letter → Letter
  | first => firstInv
  | firstInv => first
  | second => secondInv
  | secondInv => second

def value {G : Type*} [Group G] (v u : G) : Letter → G
  | first => v
  | firstInv => v⁻¹
  | second => u
  | secondInv => u⁻¹

def eval {G : Type*} [Group G] (v u : G) : List Letter → G
  | [] => 1
  | s :: w => value v u s * eval v u w

def inverseWord (w : List Letter) : List Letter := w.reverse.map inverseLetter

def powerWord (w : List Letter) : ℕ → List Letter
  | 0 => []
  | n + 1 => w ++ powerWord w n

theorem eval_append {G : Type*} [Group G] (v u : G) (w z : List Letter) :
    eval v u (w ++ z) = eval v u w * eval v u z := by
  induction w with
  | nil => simp [eval]
  | cons s w ih => simp only [List.cons_append, eval, ih, mul_assoc]

theorem eval_inverse {G : Type*} [Group G] (v u : G) (w : List Letter) :
    eval v u (inverseWord w) = (eval v u w)⁻¹ := by
  induction w with
  | nil => simp [inverseWord, eval]
  | cons s w ih =>
    have hs : value v u (inverseLetter s) = (value v u s)⁻¹ := by
      cases s <;> simp [inverseLetter, value]
    simpa only [inverseWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, eval_append, eval, mul_one, hs, mul_inv_rev] using
      congrArg (fun t => t * (value v u s)⁻¹) ih

theorem eval_power {G : Type*} [Group G] (v u : G) (w : List Letter) (n : ℕ) :
    eval v u (powerWord w n) = (eval v u w) ^ n := by
  induction n with
  | zero => simp [powerWord, eval]
  | succ n ih => simp only [powerWord, eval_append, ih, pow_succ']

def pointLetter {X : Type*} (vf vi uf ui : X → X) : Letter → X → X
  | first => vf
  | firstInv => vi
  | second => uf
  | secondInv => ui

def applyWord {X : Type*} (vf vi uf ui : X → X) : List Letter → X → X
  | [], p => p
  | s :: w, p => pointLetter vf vi uf ui s (applyWord vf vi uf ui w p)

theorem applyWord_eq {X : Type*} (v u : Equiv.Perm X) (w : List Letter) (p : X) :
    applyWord v v.symm u u.symm w p = eval v u w p := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    have hs : pointLetter v v.symm u u.symm s = ((value (G := Equiv.Perm X) v u s : Equiv.Perm X) : X → X) := by
      cases s <;> rfl
    change pointLetter v v.symm u u.symm s (applyWord v v.symm u u.symm w p) =
      value v u s (eval v u w p)
    rw [ih, hs]

theorem applyWord_eq_of_maps {X : Type*} (v u : Equiv.Perm X)
    (vf vi uf ui : X → X) (hvf : vf = v) (hvi : vi = v.symm)
    (huf : uf = u) (hui : ui = u.symm) (w : List Letter) (p : X) :
    applyWord vf vi uf ui w p = eval v u w p := by
  subst vf
  subst vi
  subst uf
  subst ui
  exact applyWord_eq v u w p

end SymmetricSubgroupAsymptotics.SignedPermutationWordPointEvaluation
