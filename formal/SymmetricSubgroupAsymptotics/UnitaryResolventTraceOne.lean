import Mathlib.Algebra.Star.Basic

/-! An actual unitary operator with invertible A+1 supplies a trace-one
resolvent. These identities hold in a possibly noncommutative star ring;
no field, finite-group or automorphism theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.UnitaryResolventTraceOne
variable {R : Type*} [Ring R] [StarRing R]

theorem star_shiftUnit (a b : Rˣ) (ha : star (a:R)=(↑(a⁻¹):R))
    (hb : (b:R)=(a:R)+1) : star b=a⁻¹*b := by
  apply Units.ext
  change star (b:R)=(↑(a⁻¹):R)*(b:R)
  rw [hb,star_add,star_one,ha,mul_add,Units.inv_mul,mul_one]
  exact add_comm _ _

theorem inverse_shift_trace_one (a b : Rˣ) (ha : star (a:R)=(↑(a⁻¹):R))
    (hb : (b:R)=(a:R)+1) :
    (↑(b⁻¹):R)+star (↑(b⁻¹):R)=1 := by
  have he : star (b⁻¹)=b⁻¹*a := by
    rw [star_inv,star_shiftUnit a b ha hb,mul_inv_rev,inv_inv]
  have hv : star (↑(b⁻¹):R)=(↑(b⁻¹):R)*(a:R) := by
    rw [←Units.coe_star,he,Units.val_mul]
  rw [hv]
  calc
    _ = (↑(b⁻¹):R)*((a:R)+1) := by rw [mul_add,mul_one]; exact add_comm _ _
    _ = (↑(b⁻¹):R)*(b:R) := congrArg (fun x:R => (↑(b⁻¹):R)*x) hb.symm
    _ = 1 := Units.inv_mul b

end SymmetricSubgroupAsymptotics.UnitaryResolventTraceOne
