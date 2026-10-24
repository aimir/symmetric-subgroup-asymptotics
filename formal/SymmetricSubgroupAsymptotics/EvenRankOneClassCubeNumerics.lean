import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The class-plus-field-exponent cube is paid uniformly at every
binary field order from eight onward. The exponent induction retains
the literal field degree e: the component grows by at most three,
whereas the degree budget gains a factor 5^(2^e). -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.EvenRankOneClassCubeNumerics

theorem class_cube_le (e : ℕ) (he : 3≤e) :
    ((2^e+4)*e)^3≤5^(2^e-1) := by
  induction e,he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    let q : ℕ := 2^e
    have hq : 8≤q := by
      simpa only [show (2 : ℕ)^3=8 by decide] using
        (Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) he)
    have hp : 2^(e+1)=2*q := by
      rw [pow_succ]
      exact Nat.mul_comm _ _
    rw [hp]
    have hc : (2*q+4)*(e+1)≤3*((q+4)*e) := by
      calc
        (2*q+4)*(e+1)≤(2*(q+4))*(e+1) :=
          Nat.mul_le_mul_right _ (by omega)
        _ =(q+4)*(2*(e+1)) := by ring
        _ ≤(q+4)*(3*e) := Nat.mul_le_mul_left _ (by omega)
        _ =3*((q+4)*e) := by ring
    have h27 : 27≤5^q := (by norm_num : (27 : ℕ)≤5^3).trans
      (Nat.pow_le_pow_right (by decide : 0<(5 : ℕ)) (by omega : 3≤q))
    calc
      ((2*q+4)*(e+1))^3≤(3*((q+4)*e))^3 := Nat.pow_le_pow_left hc 3
      _ =27*(((q+4)*e)^3) := by ring
      _ ≤27*5^(q-1) := Nat.mul_le_mul_left _ ih
      _ ≤5^q*5^(q-1) := Nat.mul_le_mul_right _ h27
      _ =5^(2*q-1) := by
        rw [← pow_add]
        congr 1
        omega

end SymmetricSubgroupAsymptotics.EvenRankOneClassCubeNumerics
