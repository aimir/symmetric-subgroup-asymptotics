import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Range

/-! Finite transition certificates for an actual action. The transition
order is application order, hence the corresponding group product is
reversed. No faithfulness or group-specific relation is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFiniteActionPathCertificate

theorem foldl_range_eq_of_steps {V : Type*} (f : ℕ→V→V) (v : ℕ→V) (N : ℕ)
    (hstep : ∀n,n<N→f n (v n)=v (n+1)) :
    (List.range N).foldl (fun x n=>f n x) (v 0)=v N := by
  have aux : ∀n,n≤N→(List.range n).foldl (fun x i=>f i x) (v 0)=v n := by
    intro n
    induction n with
    | zero => intro _;rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ,List.foldl_append]
      simp only [List.foldl_cons,List.foldl_nil]
      rw [ih (Nat.le_trans (Nat.le_succ n) hn)]
      exact hstep n (Nat.lt_of_succ_le hn)
  exact aux N le_rfl

theorem foldl_eq_reverse_product {G V : Type*} [Monoid G]
    (act : G→V→V) (hone : ∀x,act 1 x=x)
    (hmul : ∀g h x,act (g*h) x=act g (act h x)) (l : List G) (x : V) :
    l.foldl (fun v g=>act g v) x=act l.reverse.prod x := by
  induction l generalizing x with
  | nil => exact (hone x).symm
  | cons g l ih =>
    rw [List.foldl_cons,ih,List.reverse_cons,List.prod_append]
    simp only [List.prod_cons,List.prod_nil,mul_one]
    exact (hmul _ _ _).symm

end SymmetricSubgroupAsymptotics.CFSGFiniteActionPathCertificate
