import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Data.Fin.Basic

/-! Regroup three orthogonal rank-one root words without interchanging
the two factors at the same node. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalTripleRankOneWord

private theorem triple_product {G : Type*} [Monoid G] (a b : Fin 3 → G)
    (h10 : Commute (a 1) (b 0)) (h20 : Commute (a 2) (b 0))
    (h21 : Commute (a 2) (b 1)) :
    (a 0*a 1*a 2)*(b 0*b 1*b 2) =
      (a 0*b 0)*(a 1*b 1)*(a 2*b 2) := by
  calc
    _ = (a 0*a 1)*(b 0*b 1)*(a 2*b 2) :=
      (h20.mul_right h21).mul_mul_mul_comm _ _
    _ = _ := congrArg (fun x => x*(a 2*b 2))
      (h10.mul_mul_mul_comm (a 0) (b 1))

theorem rank_one_triple {G : Type*} [Monoid G] (a b : Fin 3 → G)
    (haa : ∀ i j,i ≠ j → Commute (a i) (a j))
    (hab : ∀ i j,i ≠ j → Commute (a i) (b j)) :
    (a 0*a 1*a 2)*(b 0*b 1*b 2)*(a 0*a 1*a 2) =
      (a 0*b 0*a 0)*(a 1*b 1*a 1)*(a 2*b 2*a 2) := by
  rw [triple_product a b (hab 1 0 (by decide)) (hab 2 0 (by decide))
    (hab 2 1 (by decide))]
  have hcomm (i j : Fin 3) (hij : i ≠ j) : Commute (a i*b i) (a j) :=
    (haa i j hij).mul_left (hab j i (Ne.symm hij)).symm
  exact triple_product (fun i => a i*b i) a
    (hcomm 1 0 (by decide)) (hcomm 2 0 (by decide)) (hcomm 2 1 (by decide))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalTripleRankOneWord
