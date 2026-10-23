import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoScalars
import SymmetricSubgroupAsymptotics.CFSGFixedScalarCrossRigidity
import Mathlib.Tactic.LinearCombination

/-! Scalar-centroid reconstruction from the actual Hermitian rank-one
lines. Additivity and preservation of each individual fixed-scalar root
line force ONE common scalar. No fixed-field linearity of the map is
assumed. Polarization and a genuine trace-one element work in
characteristic two as well as odd characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

theorem constant_ray_coefficient (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hnonfixed : ∃ t, sigma t ≠ t)
    (psi : parameters sigma →+ parameters sigma)
    (haxis : ∀ (a : K) (ha : sigma a = a),
      ∃ (b : K) (hb : sigma b = b), psi (axis1 sigma a ha) = axis1 sigma b hb)
    (a : K) (ha : sigma a = a) (b : K → K)
    (hb : ∀ x, sigma (b x) = b x)
    (he : ∀ x, psi (fixedScaleHom sigma a ha (ray sigma hsigma x)) =
      fixedScaleHom sigma (b x) (hb x) (ray sigma hsigma x)) :
    ∀ x, b x = b 0 := by
  have hpol (x y : K) :
      fixedScaleHom sigma (b (x + y)) (hb (x + y)) (ray sigma hsigma (x + y)) -
        fixedScaleHom sigma (b x) (hb x) (ray sigma hsigma x) -
        fixedScaleHom sigma (b y) (hb y) (ray sigma hsigma y) +
        fixedScaleHom sigma (b 0) (hb 0) (ray sigma hsigma 0) =
      psi (axis1 sigma (a * (x * sigma y + y * sigma x))
        (by rw [map_mul, ha, tracePair_fixed sigma hsigma])) := by
    have hh := congrArg psi (congrArg (fixedScaleHom sigma a ha)
      (ray_polar sigma hsigma x y))
    simpa only [map_add, map_sub, he, fixedScaleHom_axis1] using hh
  have hadd (x y : K) : b (x + y) + b 0 = b x + b y := by
    obtain ⟨d, hd, hpd⟩ := haxis (a * (x * sigma y + y * sigma x))
      (by rw [map_mul, ha, tracePair_fixed sigma hsigma])
    have hh := hpol x y
    rw [hpd] at hh
    have h00 := congrArg (fun A : parameters sigma => A.val 0 0) hh
    change b (x + y) * 1 - b x * 1 - b y * 1 + b 0 * 1 = 0 at h00
    linear_combination h00
  have hweighted (x y : K) : b (x + y) * (x + y) = b x * x + b y * y := by
    obtain ⟨d, hd, hpd⟩ := haxis (a * (x * sigma y + y * sigma x))
      (by rw [map_mul, ha, tracePair_fixed sigma hsigma])
    have hh := hpol x y
    rw [hpd] at hh
    have h01 := congrArg (fun A : parameters sigma => A.val 0 1) hh
    change b (x + y) * (x + y) - b x * x - b y * y + b 0 * 0 = 0 at h01
    linear_combination h01
  exact CFSGFixedScalarCrossRigidity.constant_of_polar_coordinates sigma hnonfixed b hb hadd hweighted

private theorem scaled_polar (sigma : K ≃+* K) (hsigma : ∀ x, sigma (sigma x) = x)
    (c : K) (hc : sigma c = c) (x y : K) :
    fixedScaleHom sigma c hc (ray sigma hsigma (x + y)) -
      fixedScaleHom sigma c hc (ray sigma hsigma x) -
      fixedScaleHom sigma c hc (ray sigma hsigma y) +
      fixedScaleHom sigma c hc (ray sigma hsigma 0) =
    axis1 sigma (c * (x * sigma y + y * sigma x))
      (by rw [map_mul, hc, tracePair_fixed sigma hsigma]) := by
  have hh := congrArg (fixedScaleHom sigma c hc) (ray_polar sigma hsigma x y)
  simpa only [map_add, map_sub, fixedScaleHom_axis1] using hh

theorem scalar_of_ray_lines (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hnonfixed : ∃ t, sigma t ≠ t)
    (theta : K) (htheta : theta + sigma theta = 1)
    (psi : parameters sigma →+ parameters sigma)
    (haxis : ∀ (a : K) (ha : sigma a = a),
      ∃ (b : K) (hb : sigma b = b), psi (axis1 sigma a ha) = axis1 sigma b hb)
    (hray : ∀ (a : K) (ha : sigma a = a) (x : K),
      ∃ (b : K) (hb : sigma b = b),
        psi (fixedScaleHom sigma a ha (ray sigma hsigma x)) =
          fixedScaleHom sigma b hb (ray sigma hsigma x)) :
    ∃ (c : K) (hc : sigma c = c), psi = fixedScaleHom sigma c hc := by
  classical
  have hconst (a : K) (ha : sigma a = a) :
      ∃ (b : K) (hb : sigma b = b), ∀ x,
        psi (fixedScaleHom sigma a ha (ray sigma hsigma x)) =
          fixedScaleHom sigma b hb (ray sigma hsigma x) := by
    choose b hb he using hray a ha
    have hbconst := constant_ray_coefficient sigma hsigma hnonfixed psi haxis a ha b hb he
    refine ⟨b 0, hb 0, ?_⟩
    intro x
    simpa only [hbconst x] using he x
  obtain ⟨c, hc, hcone⟩ := hconst 1 (map_one sigma)
  have hr (x : K) : psi (ray sigma hsigma x) =
      fixedScaleHom sigma c hc (ray sigma hsigma x) := by
    simpa only [fixedScaleHom_one] using hcone x
  have htrace (a : K) (ha : sigma a = a) :
      (1 : K) * sigma (a * theta) + (a * theta) * sigma 1 = a := by
    rw [map_mul, ha, map_one]
    calc
      _ = a * (theta + sigma theta) := by ring
      _ = a := by rw [htheta, mul_one]
  have haxis_exact (a : K) (ha : sigma a = a) :
      psi (axis1 sigma a ha) = fixedScaleHom sigma c hc (axis1 sigma a ha) := by
    have hh := congrArg psi (ray_polar sigma hsigma 1 (a * theta))
    simp only [htrace a ha] at hh
    simp only [map_add, map_sub, hr] at hh
    exact hh.symm.trans ((scaled_polar sigma hsigma c hc 1 (a * theta)).trans
      (by simp only [htrace a ha, fixedScaleHom_axis1]))
  have hscaled_ray (a : K) (ha : sigma a = a) (x : K) :
      psi (fixedScaleHom sigma a ha (ray sigma hsigma x)) =
        fixedScaleHom sigma c hc (fixedScaleHom sigma a ha (ray sigma hsigma x)) := by
    obtain ⟨b, hb, hcb⟩ := hconst a ha
    have hh := congrArg psi (congrArg (fixedScaleHom sigma a ha)
      (ray_polar sigma hsigma 1 theta))
    simp only [map_add, map_sub, hcb, fixedScaleHom_axis1] at hh
    have ht : (1 : K) * sigma theta + theta * sigma 1 = 1 := by
      simpa only [map_one, one_mul, mul_one, add_comm] using htheta
    simp only [ht, mul_one] at hh
    rw [haxis_exact, fixedScaleHom_axis1] at hh
    have hp := scaled_polar sigma hsigma b hb 1 theta
    simp only [ht, mul_one] at hp
    have heq := hp.symm.trans hh
    have he := congrArg (fun A : parameters sigma => A.val 1 1) heq
    change b = c * a at he
    rw [hcb, fixedScaleHom_mul]
    simp only [he]
  refine ⟨c, hc, ?_⟩
  apply AddMonoidHom.ext
  intro A
  have h0 (a : K) (ha : sigma a = a) :
      psi (axis0 sigma a ha) = fixedScaleHom sigma c hc (axis0 sigma a ha) := by
    rw [axis0_eq_scaled_ray_zero sigma hsigma a ha]
    exact hscaled_ray a ha 0
  rw [ray_decomposition sigma hsigma A]
  simp only [map_add, map_sub, h0, hr, haxis_exact]

theorem scalar_of_rankOne_lines (sigma : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hnonfixed : ∃ t, sigma t ≠ t)
    (theta : K) (htheta : theta + sigma theta = 1)
    (psi : parameters sigma →+ parameters sigma)
    (hline : ∀ (a : K) (ha : sigma a = a) (v : Fin 2 → K),
      ∃ (b : K) (hb : sigma b = b),
        psi (rankOneParameter sigma hsigma a ha v) = rankOneParameter sigma hsigma b hb v) :
    ∃ (c : K) (hc : sigma c = c), psi = fixedScaleHom sigma c hc := by
  apply scalar_of_ray_lines sigma hsigma hnonfixed theta htheta psi
  · intro a ha
    obtain ⟨b, hb, he⟩ := hline a ha ![0, 1]
    exact ⟨b, hb, by simpa only [← axis1_eq_rankOne sigma hsigma] using he⟩
  · intro a ha x
    obtain ⟨b, hb, he⟩ := hline a ha ![1, sigma x]
    exact ⟨b, hb, by simpa only [← fixedScaleHom_ray sigma hsigma] using he⟩

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
