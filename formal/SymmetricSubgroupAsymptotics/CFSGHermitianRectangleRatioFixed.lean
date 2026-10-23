import SymmetricSubgroupAsymptotics.CFSGHermitianIsotropicRectangle
import Mathlib.Tactic.LinearCombination

/-! A common mixed-ray ratio preserving an isotropic rectangle is fixed
by the actual field involution. This supplies the missing similitude
condition in the normalization, in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem hermitian_rectangle_mixed_ratio_fixed (sigma : K ≃+* K) (H : Matrix I I K)
    (x u y z : I → K) (t : K)
    (hxu : hermitianPair sigma H x u = 0) (hyz : hermitianPair sigma H y z = 0)
    (hxz : hermitianPair sigma H x z ≠ 0)
    (hsource : hermitianPair sigma H (x + y) (u + z) = 0)
    (himage : hermitianPair sigma H (x + t • y) (u + t • z) = 0) : sigma t = t := by
  rw [hermitianPair_add_left,hermitianPair_add_right,hermitianPair_add_right,hxu,hyz,
    zero_add,add_zero] at hsource
  have hxtz := hermitianPair_smul sigma H 1 t x z
  have htyu := hermitianPair_smul sigma H t 1 y u
  have htytz := hermitianPair_smul sigma H t t y z
  simp only [one_smul,map_one,one_mul,mul_one,hyz,mul_zero] at hxtz htyu htytz
  rw [hermitianPair_add_left,hermitianPair_add_right,hermitianPair_add_right,
    hxu,hxtz,htyu,htytz,zero_add,add_zero] at himage
  have he : (sigma t - t) * hermitianPair sigma H x z = 0 := by
    linear_combination sigma t * hsource - himage
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hxz)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
