import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! An explicit K-linear correction into two Hermitian perpendicular
spaces. On the hyperbolic residue it preserves the ACTUAL sesquilinear
pairing, with no bilinear substitution or Witt-extension assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTransverseCorrection
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I V : Type*} [Field K] [Fintype I] [AddCommGroup V] [Module K V]

def correction (sigma : K ≃+* K) (H : Matrix I I K)
    (e w : I → K) (j : V →ₗ[K] (I → K)) : V →ₗ[K] (I → K) :=
  j - (((hermitianPair sigma H w e)⁻¹) • ((pairRightLinear sigma H w).comp j)).smulRight e

theorem correction_apply (sigma : K ≃+* K) (H : Matrix I I K)
    (e w : I → K) (j : V →ₗ[K] (I → K)) (z : V) :
    correction sigma H e w j z =
      j z - ((hermitianPair sigma H w e)⁻¹ * hermitianPair sigma H w (j z)) • e := rfl

private theorem pair_sub_left (sigma : K ≃+* K) (H : Matrix I I K)
    (x y z : I → K) : hermitianPair sigma H (x - y) z =
      hermitianPair sigma H x z - hermitianPair sigma H y z := by
  apply eq_sub_iff_add_eq.mpr
  have hh := hermitianPair_add_left sigma H (x - y) y z
  rw [sub_add_cancel] at hh
  exact hh.symm

private theorem pair_sub_right (sigma : K ≃+* K) (H : Matrix I I K)
    (x y z : I → K) : hermitianPair sigma H x (y - z) =
      hermitianPair sigma H x y - hermitianPair sigma H x z :=
  (pairRightLinear sigma H x).map_sub y z

private theorem pair_smul_left (sigma : K ≃+* K) (H : Matrix I I K)
    (a : K) (x y : I → K) : hermitianPair sigma H (a • x) y = sigma a * hermitianPair sigma H x y := by
  simpa only [one_smul, mul_one] using hermitianPair_smul sigma H a 1 x y

private theorem pair_smul_right (sigma : K ≃+* K) (H : Matrix I I K)
    (a : K) (x y : I → K) : hermitianPair sigma H x (a • y) = a * hermitianPair sigma H x y := by
  simpa only [one_smul, map_one, one_mul] using hermitianPair_smul sigma H 1 a x y

theorem correction_orthogonal (sigma : K ≃+* K) (H : Matrix I I K)
    (e w : I → K) (j : V →ₗ[K] (I → K)) (hc : hermitianPair sigma H w e ≠ 0) (z : V) :
    hermitianPair sigma H w (correction sigma H e w j z) = 0 := by
  rw [correction_apply, pair_sub_right]
  have hs := hermitianPair_smul sigma H 1
    ((hermitianPair sigma H w e)⁻¹ * hermitianPair sigma H w (j z)) w e
  simp only [one_smul, map_one, one_mul] at hs
  rw [hs]
  field_simp [hc] <;> ring

theorem correction_pairing (sigma : K ≃+* K) (H : Matrix I I K)
    (e w : I → K) (j : V →ₗ[K] (I → K)) (hee : hermitianPair sigma H e e = 0)
    (he : ∀ z, hermitianPair sigma H e (j z) = 0)
    (he' : ∀ z, hermitianPair sigma H (j z) e = 0) (z z' : V) :
    hermitianPair sigma H (correction sigma H e w j z) (correction sigma H e w j z') =
      hermitianPair sigma H (j z) (j z') := by
  simp only [correction_apply, pair_sub_left, pair_sub_right, pair_smul_left, pair_smul_right,
    he, he', hee, mul_zero, sub_zero]

theorem correction_leftInverse (sigma : K ≃+* K) (H : Matrix I I K)
    (e w : I → K) (j : V →ₗ[K] (I → K)) (pi : (I → K) →ₗ[K] V)
    (hj : ∀ z, pi (j z) = z) (he : pi e = 0) (z : V) :
    pi (correction sigma H e w j z) = z := by
  rw [correction_apply, map_sub, map_smul, hj, he, smul_zero, sub_zero]

theorem correction_injective (sigma : K ≃+* K) (H : Matrix I I K)
    (e w : I → K) (j : V →ₗ[K] (I → K)) (pi : (I → K) →ₗ[K] V)
    (hj : ∀ z, pi (j z) = z) (he : pi e = 0) :
    Function.Injective (correction sigma H e w j) := by
  intro z z' hz
  have hh := congrArg pi hz
  simpa only [correction_leftInverse sigma H e w j pi hj he] using hh

theorem correction_orthogonal_to (sigma : K ≃+* K) (H : Matrix I I K)
    (e w u : I → K) (j : V →ₗ[K] (I → K))
    (hue : hermitianPair sigma H u e = 0) (huj : ∀ z, hermitianPair sigma H u (j z) = 0) (z : V) :
    hermitianPair sigma H u (correction sigma H e w j z) = 0 := by
  rw [correction_apply, pair_sub_right]
  have hs := hermitianPair_smul sigma H 1
    ((hermitianPair sigma H w e)⁻¹ * hermitianPair sigma H w (j z)) u e
  simp only [one_smul, map_one, one_mul, hue, mul_zero] at hs
  rw [hs, huj, sub_zero]

end SymmetricSubgroupAsymptotics.CFSGHermitianTransverseCorrection
