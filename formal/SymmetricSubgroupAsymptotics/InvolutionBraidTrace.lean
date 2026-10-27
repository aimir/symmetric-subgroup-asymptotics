import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.Group

/-! A small certificate verifier for ONLY involution cancellation,
commutation and simply-laced length-three braids.  Its soundness needs
no faithful root representation, finite Coxeter recognition or group
order. Every stored step carries its literal prefix and suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.InvolutionBraidTrace

inductive Kind where
  | cancel | commute | braid
  deriving DecidableEq, Repr

structure Step (ι : Type*) where
  kind : Kind
  prefixWord : List ι
  suffixWord : List ι
  i : ι
  j : ι
  deriving DecidableEq, Repr

def leftCore {ι : Type*} (s : Step ι) : List ι :=
  match s.kind with
  | .cancel => [s.i, s.i]
  | .commute => [s.i, s.j]
  | .braid => [s.i, s.j, s.i]

def rightCore {ι : Type*} (s : Step ι) : List ι :=
  match s.kind with
  | .cancel => []
  | .commute => [s.j, s.i]
  | .braid => [s.j, s.i, s.j]

def before {ι : Type*} (s : Step ι) : List ι := s.prefixWord ++ leftCore s ++ s.suffixWord
def after {ι : Type*} (s : Step ι) : List ι := s.prefixWord ++ rightCore s ++ s.suffixWord

def legal {ι : Type*} (adj : ι → ι → Bool) (s : Step ι) : Bool :=
  match s.kind with
  | .cancel => true
  | .commute => !adj s.i s.j
  | .braid => adj s.i s.j

def value {ι G : Type*} [Monoid G] (g : ι → G) (w : List ι) : G := (w.map g).prod

theorem value_append {ι G : Type*} [Monoid G] (g : ι → G) (u v : List ι) :
    value g (u ++ v) = value g u * value g v := by
  simp only [value, List.map_append, List.prod_append]

theorem value_reverse {ι G : Type*} [Group G] (g : ι → G)
    (hsq : ∀ i, g i * g i = 1) (w : List ι) :
    value g w.reverse = (value g w)⁻¹ := by
  induction w with
  | nil => simp [value]
  | cons i tail ih =>
    have hi : (g i)⁻¹ = g i := inv_eq_of_mul_eq_one_right (hsq i)
    simp only [List.reverse_cons, value_append, ih]
    simpa only [value, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_inv_rev, hi]

theorem step_sound {ι G : Type*} [Group G]
    (adj : ι → ι → Bool) (g : ι → G)
    (hsq : ∀ i, g i * g i = 1)
    (hc : ∀ i j, adj i j = false → g i * g j = g j * g i)
    (hb : ∀ i j, adj i j = true → g i * g j * g i = g j * g i * g j)
    (s : Step ι) (hlegal : legal adj s = true) :
    value g (before s) = value g (after s) := by
  have hcore : value g (leftCore s) = value g (rightCore s) := by
    rcases s with ⟨kind, prefixWord, suffixWord, i, j⟩
    cases kind with
    | cancel => simpa [leftCore, rightCore, value] using hsq i
    | commute =>
      have hij : adj i j = false := by
        cases h : adj i j <;> simp_all [legal]
      simpa [leftCore, rightCore, value] using hc i j hij
    | braid =>
      have hij : adj i j = true := hlegal
      simpa [leftCore, rightCore, value, mul_assoc] using hb i j hij
  simp only [before, after, value_append]
  rw [hcore]

def checkTo {ι : Type*} [DecidableEq ι] (adj : ι → ι → Bool)
    (w : List ι) (steps : List (Step ι)) (finish : List ι) : Bool :=
  match steps with
  | [] => decide (w = finish)
  | s :: tail => legal adj s && decide (before s = w) && checkTo adj (after s) tail finish

theorem checkTo_sound {ι G : Type*} [DecidableEq ι] [Group G]
    (adj : ι → ι → Bool) (g : ι → G)
    (hsq : ∀ i, g i * g i = 1)
    (hc : ∀ i j, adj i j = false → g i * g j = g j * g i)
    (hb : ∀ i j, adj i j = true → g i * g j * g i = g j * g i * g j)
    (w : List ι) (steps : List (Step ι)) (finish : List ι)
    (h : checkTo adj w steps finish = true) : value g w = value g finish := by
  induction steps generalizing w with
  | nil =>
    have hw : w = finish := of_decide_eq_true h
    subst w
    rfl
  | cons s tail ih =>
    simp only [checkTo, Bool.and_eq_true_eq_eq_true_and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hlegal, hbefore⟩, htail⟩
    calc
      value g w = value g (before s) := by rw [hbefore]
      _ = value g (after s) := step_sound adj g hsq hc hb s hlegal
      _ = value g finish := ih (after s) htail

def check {ι : Type*} [DecidableEq ι] (adj : ι → ι → Bool)
    (w : List ι) (steps : List (Step ι)) : Bool := checkTo adj w steps []

theorem check_sound {ι G : Type*} [DecidableEq ι] [Group G]
    (adj : ι → ι → Bool) (g : ι → G)
    (hsq : ∀ i, g i * g i = 1)
    (hc : ∀ i j, adj i j = false → g i * g j = g j * g i)
    (hb : ∀ i j, adj i j = true → g i * g j * g i = g j * g i * g j)
    (w : List ι) (steps : List (Step ι)) (h : check adj w steps = true) :
    value g w = 1 :=
  checkTo_sound adj g hsq hc hb w steps [] h

end SymmetricSubgroupAsymptotics.InvolutionBraidTrace
