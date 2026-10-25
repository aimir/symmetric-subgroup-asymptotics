import SymmetricSubgroupAsymptotics.QuadraticExponentialPolynomialTail
import Mathlib.Tactic.Zify

/-! Arithmetic envelopes for norm shells and ordered orthonormal frames.
The recurrence and frame-step hypotheses are explicit interfaces for
actual counting lemmas, not assumed group-order estimates. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.FiniteHermitianFrameEnvelope

theorem shell_two_sided (q : ℕ) (hq : 2 ≤ q) (B : ℕ → ℕ)
    (hzero : B 0=0)
    (hstep : ∀ n, B (n+1)+q*B n=(q+1)*q^(2*n)) (n : ℕ) :
    B (n+1) ≤ q^(2*n+1)+q^n ∧ q^(2*n+1) ≤ B (n+1)+q^n := by
  induction n with
  | zero =>
    have hh : B 1=q+1 := by simpa [hzero] using hstep 0
    simpa only [Nat.reduceMul,Nat.reduceAdd,pow_one,pow_zero] using
      (show B 1 ≤ q+1 ∧ q ≤ B 1+1 from by omega)
  | succ n ih =>
    have hh := hstep (n+1)
    have he : q^(2*(n+1))=q^(2*n+1)*q := by
      rw [show 2*(n+1)=(2*n+1)+1 by omega,pow_succ]
    have he2 : q^(2*(n+1)+1)=q^(2*n+1)*q^2 := by
      rw [show 2*(n+1)+1=(2*n+1)+2 by omega,pow_add]
    rw [he] at hh
    rw [he2,pow_succ q n]
    have hu := Nat.mul_le_mul_left q ih.1
    have hl := Nat.mul_le_mul_left q ih.2
    constructor <;> nlinarith

private theorem geometric_step (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    (t-1)*(t*q+1) ≤ t*(t*q-1) := by
  have htq : 1 ≤ t*q := by nlinarith
  have hqz : (2:ℤ) ≤ q := by omega
  have htz : (1:ℤ) ≤ t := by omega
  zify [ht,htq]
  nlinarith

theorem frame_strong (q : ℕ) (hq : 2 ≤ q) (B C : ℕ → ℕ)
    (hBzero : B 0=0)
    (hBstep : ∀ n, B (n+1)+q*B n=(q+1)*q^(2*n))
    (hCzero : C 0=1) (hCstep : ∀ n, C (n+1) ≤ B (n+1)*C n)
    (n : ℕ) (hn : 1 ≤ n) :
    C n*q^n ≤ 3*q^(n^2)*(q^n-1) := by
  induction n,hn using Nat.le_induction with
  | base =>
    have hb := hBstep 0
    simp only [hBzero,mul_zero,add_zero,pow_zero,mul_one] at hb
    have hc := hCstep 0
    rw [hCzero,mul_one,hb] at hc
    norm_num only [pow_one,Nat.one_pow] at *
    have hs : q-1+1=q := by omega
    nlinarith
  | succ n hn ih =>
    have hb := (shell_two_sided q hq B hBzero hBstep n).1
    have hg := geometric_step q (q^n) hq (Nat.one_le_pow _ _ (by omega))
    rw [←pow_succ] at hg
    have he : q^(2*n+1)=q^n*q^(n+1) := by
      rw [←pow_add]
      congr 1
      omega
    calc
      C (n+1)*q^(n+1) ≤ (B (n+1)*C n)*q^(n+1) :=
        Nat.mul_le_mul_right _ (hCstep n)
      _ ≤ (q^(2*n+1)+q^n)*C n*q^(n+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb)
      _ = (C n*q^n)*((q^(n+1)+1)*q^(n+1)) := by rw [he]; ring
      _ ≤ (3*q^(n^2)*(q^n-1))*((q^(n+1)+1)*q^(n+1)) :=
        Nat.mul_le_mul_right _ ih
      _ = 3*q^(n^2)*((q^n-1)*(q^(n+1)+1))*q^(n+1) := by ring
      _ ≤ 3*q^(n^2)*(q^n*(q^(n+1)-1))*q^(n+1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hg)
      _ = 3*q^((n+1)^2)*(q^(n+1)-1) := by
        rw [show (n+1)^2=n^2+n+(n+1) by ring,
          pow_add q (n^2+n) (n+1),pow_add q (n^2) n]
        ring

theorem frame_card_le (q : ℕ) (hq : 2 ≤ q) (B C : ℕ → ℕ)
    (hBzero : B 0=0)
    (hBstep : ∀ n, B (n+1)+q*B n=(q+1)*q^(2*n))
    (hCzero : C 0=1) (hCstep : ∀ n, C (n+1) ≤ B (n+1)*C n) (n : ℕ) :
    C n ≤ 3*q^(n^2) := by
  by_cases hn : n=0
  · subst n
    simp [hCzero]
  · have hh := frame_strong q hq B C hBzero hBstep hCzero hCstep n (by omega)
    have hu := Nat.mul_le_mul_left (3*q^(n^2)) (Nat.sub_le (q^n) 1)
    have hp : 0 < q^n := Nat.pow_pos (by omega)
    nlinarith

end SymmetricSubgroupAsymptotics.FiniteHermitianFrameEnvelope
