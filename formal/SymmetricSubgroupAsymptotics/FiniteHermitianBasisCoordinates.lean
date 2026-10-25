import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-! Coordinates of a genuinely orthonormal basis and a literal tail
sum. These identities provide the geometric encoding used by prefix
stabilizers, independently of any group order or shell estimate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteHermitianBasisCoordinates
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}

def coordinatePair (sigma : K ≃+* K) (b : Basis (Fin n) K V) (x y : V) : K :=
  ∑ i, sigma (b.repr x i)*b.repr y i

theorem coordinatePair_basis_left (sigma : K ≃+* K) (b : Basis (Fin n) K V)
    (i : Fin n) (x : V) : coordinatePair sigma b (b i) x=b.repr x i := by
  classical
  simp only [coordinatePair,b.repr_self]
  rw [Finset.sum_eq_single i]
  · simp [Finsupp.single_apply]
  · intro j _ hji
    simp [Finsupp.single_apply,hji,Ne.symm hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private def tailEquiv (k : ℕ) (hk : k ≤ n) :
    Fin (n-k) ≃ {i : Fin n // ¬ i.val < k} where
  toFun j := ⟨⟨k+j.val,by omega⟩,by dsimp; omega⟩
  invFun i := ⟨i.val.val-k,by have := i.val.isLt; have := i.property; omega⟩
  left_inv j := by
    apply Fin.ext
    dsimp
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    dsimp
    have := i.property
    omega

theorem sum_tail_of_prefix_zero {F : Type*} [AddCommMonoid F]
    (f : Fin n → K) (N : K → F) (hN : N 0=0) (k : ℕ) (hk : k ≤ n)
    (hf : ∀ i : Fin n, i.val < k → f i=0) :
    (∑ i : Fin n, N (f i)) =
      ∑ j : Fin (n-k), N (f ⟨k+j.val,by omega⟩) := by
  classical
  have hz : (∑ i : {i : Fin n // i.val < k}, N (f i.val))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hf i.val i.property,hN]
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i.val < k)
    (fun i : Fin n => N (f i))
  rw [hz,zero_add] at hs
  calc
    _ = ∑ i : {i : Fin n // ¬i.val < k}, N (f i.val) := hs.symm
    _ = ∑ j : Fin (n-k), N (f ((tailEquiv k hk) j).val) :=
      (Equiv.sum_comp (tailEquiv k hk) (fun i => N (f i.val))).symm
    _ = _ := rfl

theorem norm_tail_of_prefix_zero (sigma : K ≃+* K) (b : Basis (Fin n) K V)
    (x : V) (k : ℕ) (hk : k ≤ n)
    (hx : ∀ i : Fin n, i.val < k → b.repr x i=0) :
    coordinatePair sigma b x x =
      ∑ j : Fin (n-k), sigma (b.repr x ⟨k+j.val,by omega⟩)*
        b.repr x ⟨k+j.val,by omega⟩ :=
  sum_tail_of_prefix_zero (fun i => b.repr x i) (fun a => sigma a*a)
    (by simp only [mul_zero]) k hk hx

end SymmetricSubgroupAsymptotics.FiniteHermitianBasisCoordinates
