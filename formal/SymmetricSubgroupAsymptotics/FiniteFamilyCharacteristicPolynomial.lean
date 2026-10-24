import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin

/-! The characteristic polynomial of an actual finite coordinate
product of endomorphisms is the product of their characteristic
polynomials. Head-tail splitting proves the formula without an
assumed block decomposition or conjugacy classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.FiniteFamilyCharacteristicPolynomial
universe u v
variable (K : Type u) [Field K]

def splitFinSucc {n : ℕ} (M : Fin (n+1) → Type v)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] :
    ((i : Fin (n+1)) → M i) ≃ₗ[K] M 0 × ((i : Fin n) → M i.succ) where
  toFun x := (x 0,fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem split_conj_piMap {n : ℕ} (M : Fin (n+1) → Type v)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (A : (i : Fin (n+1)) → Module.End K (M i)) :
    (splitFinSucc K M).conj (LinearMap.piMap A) =
      (A 0).prodMap (LinearMap.piMap (fun i : Fin n => A i.succ)) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> rfl

theorem charpoly_pi_fin (n : ℕ) :
    ∀ (M : Fin n → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
      [∀ i, Module.Finite K (M i)] (A : (i : Fin n) → Module.End K (M i)),
      (LinearMap.piMap A).charpoly = ∏ i : Fin n, (A i).charpoly := by
  induction n with
  | zero =>
    intro M _ _ _ A
    have hz : LinearMap.piMap A = 0 := Subsingleton.elim _ _
    rw [hz,LinearMap.charpoly_zero,Module.finrank_zero_of_subsingleton,pow_zero] <;> simp
  | succ n ih =>
    intro M _ _ _ A
    let E := splitFinSucc K M
    have hE : E.conj (LinearMap.piMap A) =
        (A 0).prodMap (LinearMap.piMap (fun i : Fin n => A i.succ)) :=
      split_conj_piMap K M A
    calc
      _ = (E.conj (LinearMap.piMap A)).charpoly :=
        (E.charpoly_conj (LinearMap.piMap A)).symm
      _ = (A 0).charpoly * (LinearMap.piMap (fun i : Fin n => A i.succ)).charpoly := by
        rw [hE,LinearMap.charpoly_prodMap]
      _ = (A 0).charpoly * ∏ i : Fin n, (A i.succ).charpoly :=
        congrArg (fun p => (A 0).charpoly*p)
          (ih (fun i : Fin n => M i.succ) (fun i : Fin n => A i.succ))
      _ = _ := (Fin.prod_univ_succ (fun i : Fin (n+1) => (A i).charpoly)).symm

end SymmetricSubgroupAsymptotics.FiniteFamilyCharacteristicPolynomial
