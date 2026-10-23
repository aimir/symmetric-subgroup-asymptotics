import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Group
import Lean.Elab.Tactic.Omega

/-! Surjectivity of the two scalar coordinates of a cubic-norm torus.
The norm-one correction is essential: choosing the two initial scalars
alone does not give the requested first coordinate. This group-algebra
lemma does not assume that the literal torus acts by these formulas;
each model must establish its own action before applying it. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGCubicNormTorusScalars
variable {K F : Type*} [CommGroup K] [CommGroup F]

def scalarMap (embed : F →* K) (norm : K →* F) (p : K × F) : K × F :=
  (p.1 ^ 2 * (embed p.2)⁻¹, p.2 ^ 2 * (norm p.1)⁻¹)

theorem scalarMap_surjective_of_kernel_square_surjective
    (embed : F →* K) (norm : K →* F)
    (hnorm : ∀ a, norm (embed a) = a ^ 3)
    (hsquare : Function.Surjective (fun v : norm.ker => v ^ 2)) :
    Function.Surjective (scalarMap embed norm) := by
  rintro ⟨lam, mu⟩
  let delta : norm.ker := ⟨embed (norm lam) * (lam ^ 3)⁻¹, by
    change norm (embed (norm lam) * (lam ^ 3)⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hnorm, mul_inv_cancel]⟩
  obtain ⟨v, hv⟩ := hsquare delta
  have hvsq : (v : K) ^ 2 = embed (norm lam) * (lam ^ 3)⁻¹ :=
    congrArg Subtype.val hv
  refine ⟨(lam ^ 2 * embed mu * (v : K), norm lam * mu ^ 2), ?_⟩
  apply Prod.ext
  · change (lam ^ 2 * embed mu * (v : K)) ^ 2 * (embed (norm lam * mu ^ 2))⁻¹ = lam
    apply mul_inv_eq_iff_eq_mul.mpr
    simp only [mul_pow, map_mul, map_pow]
    rw [hvsq]
    calc
      _ = ((lam ^ 2) ^ 2 * (lam ^ 3)⁻¹) *
          (embed (norm lam) * embed mu ^ 2) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = lam * (embed (norm lam) * embed mu ^ 2) := by
        congr 1
        group
  · change (norm lam * mu ^ 2) ^ 2 * (norm (lam ^ 2 * embed mu * (v : K)))⁻¹ = mu
    have hNv : norm (v : K) = 1 := v.property
    simp only [map_mul, map_pow, hnorm, hNv]
    simp [pow_succ, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

theorem kernel_square_surjective_of_odd_power (embed : F →* K) (norm : K →* F)
    (m : ℕ) (hm : Odd m) (hnorm : ∀ u, embed (norm u) = u ^ m) :
    Function.Surjective (fun v : norm.ker => v ^ 2) := by
  obtain ⟨k, hk⟩ := hm
  intro delta
  have horder : (delta : K) ^ m = 1 := by
    have h := hnorm (delta : K)
    rw [delta.property, map_one] at h
    exact h.symm
  refine ⟨delta ^ (k + 1), ?_⟩
  apply Subtype.ext
  change ((delta : K) ^ (k + 1)) ^ 2 = (delta : K)
  have he : (k + 1) * 2 = m + 1 := by omega
  rw [← pow_mul, he, pow_succ, horder, one_mul]

theorem scalarMap_surjective_of_odd_norm_power
    (embed : F →* K) (norm : K →* F)
    (hnorm : ∀ a, norm (embed a) = a ^ 3)
    (m : ℕ) (hm : Odd m) (hpower : ∀ u, embed (norm u) = u ^ m) :
    Function.Surjective (scalarMap embed norm) :=
  scalarMap_surjective_of_kernel_square_surjective embed norm hnorm
    (kernel_square_surjective_of_odd_power embed norm m hm hpower)

end SymmetricSubgroupAsymptotics.CFSGCubicNormTorusScalars
