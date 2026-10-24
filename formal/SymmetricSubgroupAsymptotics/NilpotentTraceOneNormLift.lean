import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! A bounded algebraic norm lift in characteristic two. A trace-one
element supplies actual norm roots of selfadjoint unipotent elements;
the construction is a finite Artin--Schreier iteration and assumes no
norm-surjectivity or form-classification theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.NilpotentTraceOneNormLift

variable {R : Type*} [CommRing R] [CharP R 2]

def correction (c z : R) : ℕ → R
  | 0 => 0
  | k + 1 => z + c * correction c z k ^ 2

private theorem residual_step (c z a : R) :
    (z + c*a^2) + c*(z + c*a^2)^2 + z = c*(a + c*a^2 + z)^2 := by
  calc
    _ = (z+z) + c*(a + c*a^2 + z)^2 := by
      simp only [CharTwo.add_sq, mul_pow]
      ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

theorem correction_residual (c z : R) (k : ℕ) :
    correction c z k + c * correction c z k ^ 2 + z =
      c ^ (2^k-1) * z ^ (2^k) := by
  induction k with
  | zero => simp [correction]
  | succ k ih =>
    have hk : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    have he : 1 + (2^k-1)*2 = 2^(k+1)-1 := by rw [pow_succ]; omega
    change (z+c*correction c z k^2) + c*(z+c*correction c z k^2)^2 + z = _
    rw [residual_step, ih]
    calc
      _ = c^(1+(2^k-1)*2) * z^((2^k)*2) := by
        simp only [mul_pow, ← pow_mul, pow_add, pow_one]
        ring
      _ = _ := by rw [he, ← pow_succ]

theorem correction_equation (c z : R) (k : ℕ) (hz : z^(2^k)=0) :
    correction c z k + c * correction c z k ^ 2 = z := by
  have h := correction_residual c z k
  rw [hz, mul_zero] at h
  exact CharTwo.add_eq_zero.mp h

variable [StarRing R]

omit [CharP R 2] in
theorem star_correction (c z : R) (hc : star c=c) (hz : star z=z) (k : ℕ) :
    star (correction c z k) = correction c z k := by
  induction k with
  | zero => simp only [correction, star_zero]
  | succ k ih =>
    simp only [correction, star_add, star_mul, star_pow, hc, hz, ih]
    ring

theorem exists_norm_eq_one_add (u z : R) (hu : u+star u=1)
    (hz : star z=z) (k : ℕ) (hnil : z^(2^k)=0) :
    ∃ T : R, T*star T = 1+z := by
  let c := u*star u
  let a := correction c z k
  have hc : star c=c := by simp only [c, star_mul, star_star]
  have ha : star a=a := star_correction c z hc hz k
  have he : a+c*a^2=z := correction_equation c z k hnil
  refine ⟨1+u*a, ?_⟩
  calc
    _ = 1+(u+star u)*a+c*a^2 := by
      simp only [star_add, star_one, star_mul, ha]
      dsimp only [c]
      ring
    _ = 1+(a+c*a^2) := by rw [hu, one_mul]; ring
    _ = _ := congrArg (fun x : R => 1+x) he

end SymmetricSubgroupAsymptotics.NilpotentTraceOneNormLift
