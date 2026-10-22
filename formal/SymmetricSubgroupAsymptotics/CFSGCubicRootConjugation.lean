import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! A rational cubic-nilpotent exponential acts linearly on an actual
adjoint string of length two. This is a coefficient calculation, not a
global adjoint-nilpotence assumption. Integral matrix identities can be
transported to all characteristics only after a separate integral cast
argument; this theorem makes no such reduction by itself. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGCubicRootConjugation
variable {R : Type*} [Ring R] [Algebra ℚ R]

theorem conjugate_on_length_two (e x : R) (he : e^3=0) (hx : ⁅e,⁅e,x⁆⁆=0)
    (t : ℚ) (u : Rˣ) (hu : (u:R)=1+t • e+(t^2/2) • e^2) :
    (u:R)*x*((u⁻¹:Rˣ):R)=x+t • ⁅e,x⁆ := by
  let z : R := ⁅e,x⁆
  have hz : e*z=z*e := by
    change e*z-z*e=0 at hx
    exact sub_eq_zero.mp hx
  have hc : Commute e z := hz
  have hleft : e^2*z=z*e^2 := (hc.pow_left 2).eq
  have hmid : e*z*e=z*e^2 := by rw [hz]; noncomm_ring
  have htel : e^3*x-x*e^3=e^2*z+e*z*e+z*e^2 := by
    dsimp only [z]
    simp only [Ring.lie_def]
    noncomm_ring
  rw [he,zero_mul,mul_zero,sub_self,hleft,hmid] at htel
  have h3 : (3:ℚ) • (z*e^2)=0 := by
    calc
      (3:ℚ) • (z*e^2)=z*e^2+z*e^2+z*e^2 := by module
      _=0 := htel.symm
  have hze2 : z*e^2=0 := by
    have hh := congrArg (fun y : R=>(1/3:ℚ) • y) h3
    simpa only [smul_smul,show (1/3:ℚ)*3=1 by norm_num,one_smul,smul_zero] using hh
  have hex : e*x=x*e+z := by
    dsimp only [z]
    simp only [Ring.lie_def]
    noncomm_ring
  have he2x : e^2*x=x*e^2+(2:ℚ) • (z*e) := by
    calc
      e^2*x=x*e^2+(e*z+z*e) := by
        dsimp only [z]
        simp only [Ring.lie_def]
        noncomm_ring
      _=x*e^2+(2:ℚ) • (z*e) := by rw [hz]; module
  have hux : (u:R)*x=(x+t • z)*(u:R) := by
    simp only [hu]
    simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,smul_smul]
    rw [hex,he2x,hze2]
    simp only [smul_add,smul_smul,smul_zero,add_zero]
    match_scalars <;> ring
  change (u:R)*x*((u⁻¹:Rˣ):R)=x+t • z
  rw [hux,mul_assoc,Units.mul_inv,mul_one]

end SymmetricSubgroupAsymptotics.CFSGCubicRootConjugation
