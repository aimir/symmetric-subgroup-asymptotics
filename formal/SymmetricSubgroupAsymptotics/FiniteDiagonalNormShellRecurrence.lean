import SymmetricSubgroupAsymptotics.FiniteNormSumFibreRecurrence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Basic

/-! Exact fixed-norm-one counts for diagonal sums. Splitting off the
first literal coordinate binds the one-coordinate fibre recurrence.
No isometry group or orthonormal-basis existence is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteDiagonalNormShellRecurrence

variable {F K : Type*} [Field F] [Finite K]

def shellCard (N : K → F) (n : ℕ) : ℕ :=
  Nat.card {v : Fin n → K // ∑ i, N (v i)=1}

private def shellSplitEquiv (N : K → F) (n : ℕ) :
    {v : Fin (n+1) → K // ∑ i, N (v i)=1} ≃
      {p : (Fin n → K) × K // (∑ i, N (p.1 i))+N p.2=1} where
  toFun v := ⟨((fun i => v.val i.succ),v.val 0),by
    have hv := v.property
    rw [Fin.sum_univ_succ] at hv
    simpa only [add_comm] using hv⟩
  invFun p := ⟨Fin.cons p.val.2 p.val.1,by
    rw [Fin.sum_univ_succ]
    simpa only [Fin.cons_zero,Fin.cons_succ,add_comm] using p.property⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      rfl
    · rfl

theorem shellCard_zero (N : K → F) : shellCard N 0=0 := by
  simp [shellCard]

theorem shellCard_succ_recurrence (N : K → F) (q : ℕ) (hK : Nat.card K=q^2)
    (hzero : Nat.card {t : K // N t=0}=1)
    (hnonzero : ∀ a : F, a ≠ 0 → Nat.card {t : K // N t=a}=q+1) (n : ℕ) :
    shellCard N (n+1)+q*shellCard N n=(q+1)*q^(2*n) := by
  have hh := FiniteNormSumFibreRecurrence.sum_fibre_card_recurrence
    (fun v : Fin n → K => ∑ i, N (v i)) N q hzero hnonzero (1 : F)
  have hc : Nat.card (Fin n → K)=q^(2*n) := by
    rw [Nat.card_fun,Nat.card_fin,hK,←pow_mul]
  change Nat.card {v : Fin (n+1) → K // ∑ i, N (v i)=1}+
    q*Nat.card {v : Fin n → K // ∑ i, N (v i)=1}=_
  rw [Nat.card_congr (shellSplitEquiv N n)]
  exact hh.trans (congrArg (fun a : ℕ => (q+1)*a) hc)

end SymmetricSubgroupAsymptotics.FiniteDiagonalNormShellRecurrence
