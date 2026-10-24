import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! A monic self-reciprocal polynomial of degree `2r` is determined by
its coefficients at `1, …, r`. The bound is over any finite coefficient
field, and needs no factorization or conjugacy classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.MonicSelfReciprocalPolynomialCount
open Polynomial
variable (K : Type*) [Field K]

def Family (r : ℕ) :=
  {p : K[X] // p.Monic ∧ p.natDegree = 2 * r ∧ p.reverse = p}

def code {r : ℕ} (p : Family K r) : Fin r → K :=
  fun i => p.1.coeff (i.val + 1)

theorem coeff_reflection {r : ℕ} (p : Family K r) {n : ℕ} (hn : n ≤ 2*r) :
    p.1.coeff (2*r-n) = p.1.coeff n := by
  have h := congrArg (fun q : K[X] => q.coeff n) p.2.2.2
  simpa only [Polynomial.coeff_reverse, p.2.2.1, Polynomial.revAt_le hn] using h

theorem code_injective (r : ℕ) : Function.Injective (code K (r := r)) := by
  intro p q hpq
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  have htop : p.1.coeff (2*r) = q.1.coeff (2*r) := by
    have hp : p.1.coeff (2*r) = 1 := by
      simpa only [p.2.2.1] using p.2.1.coeff_natDegree
    have hq : q.1.coeff (2*r) = 1 := by
      simpa only [q.2.2.1] using q.2.1.coeff_natDegree
    exact hp.trans hq.symm
  have hlow (j : ℕ) (hj : 0 < j) (hjr : j ≤ r) :
      p.1.coeff j = q.1.coeff j := by
    have h := congrFun hpq (⟨j-1, by omega⟩ : Fin r)
    simpa only [code, show j-1+1=j by omega] using h
  by_cases hn : 2*r < n
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa only [p.2.2.1] using hn),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa only [q.2.2.1] using hn)]
  · by_cases hz : n = 0
    · subst n
      simpa only [Nat.sub_zero] using
        (coeff_reflection K p (by omega : 0 ≤ 2*r)).symm.trans
          (htop.trans (coeff_reflection K q (by omega : 0 ≤ 2*r)))
    · by_cases ht : n = 2*r
      · simpa only [ht] using htop
      · by_cases hr : n ≤ r
        · exact hlow n (by omega) hr
        · exact (coeff_reflection K p (by omega : n ≤ 2*r)).symm.trans
            ((hlow (2*r-n) (by omega) (by omega)).trans
              (coeff_reflection K q (by omega : n ≤ 2*r)))

instance finiteFamily [Finite K] (r : ℕ) : Finite (Family K r) :=
  Finite.of_injective (code K (r := r)) (code_injective K r)

theorem card_le [Finite K] (r : ℕ) : Nat.card (Family K r) ≤ Nat.card K ^ r := by
  classical
  letI := Fintype.ofFinite K
  have h := Nat.card_le_card_of_injective (code K (r := r)) (code_injective K r)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h

end SymmetricSubgroupAsymptotics.MonicSelfReciprocalPolynomialCount
