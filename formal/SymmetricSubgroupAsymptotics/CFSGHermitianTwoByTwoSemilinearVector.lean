import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOneSemilinear
import Mathlib.LinearAlgebra.Pi

/-! The vector map obtained from normalized Hermitian coefficient
rigidity is an actual injective quadratic-field semilinear map. Both
orientations of the involution are allowed, with their field map
constructed explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

def twoCoordinateSemilinearMap (tau : K ≃+* K) (alpha delta : K) :
    (Fin 2 → K) →ₛₗ[tau.toRingHom] (Fin 2 → K) where
  toFun v := ![alpha * tau (v 0), delta * tau (v 1)]
  map_add' v w := by
    ext i
    fin_cases i <;> simp [map_add, mul_add]
  map_smul' a v := by
    ext i
    fin_cases i <;> simp [map_mul, mul_left_comm, mul_assoc]

theorem twoCoordinateSemilinearMap_injective (tau : K ≃+* K)
    (alpha delta : K) (halpha : alpha ≠ 0) (hdelta : delta ≠ 0) :
    Function.Injective (twoCoordinateSemilinearMap tau alpha delta) := by
  intro v w he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  change alpha * tau (v 0) = alpha * tau (w 0) at h0
  change delta * tau (v 1) = delta * tau (w 1) at h1
  ext i
  fin_cases i
  · exact tau.injective (mul_left_cancel₀ halpha h0)
  · exact tau.injective (mul_left_cancel₀ hdelta h1)

theorem exists_normalized_cone_vector_map (sigma tau : K ≃+* K)
    (hsigma : ∀ x, sigma (sigma x) = x) (hcomm : Function.Commute sigma tau)
    (E : parameters sigma ≃+ parameters sigma)
    (hscalar : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
      E (fixedScaleHom sigma a ha A) =
        fixedScaleHom sigma (tau a) (automorphism_fixed_of_commute sigma tau hcomm a ha) (E A))
    (hcone : ∀ A : parameters sigma, A.val.det = 0 → (E A).val.det = 0)
    (alpha beta gamma : K) (halpha : sigma alpha = alpha) (hbeta : sigma beta = beta)
    (halpha0 : alpha ≠ 0) (hbeta0 : beta ≠ 0)
    (haxis0 : E (axis0 sigma 1 (map_one sigma)) = axis0 sigma alpha halpha)
    (haxis1 : E (axis1 sigma 1 (map_one sigma)) = axis1 sigma beta hbeta)
    (hgamma : gamma * sigma gamma = alpha * beta)
    (hoff : (∀ x, offDiagonalImageHom sigma hsigma E x = gamma * tau x) ∨
      (∀ x, offDiagonalImageHom sigma hsigma E x = gamma * tau (sigma x))) :
    ∃ theta : K ≃+* K, ∃ htheta : Function.Commute sigma theta,
      ∃ L : (Fin 2 → K) →ₛₗ[theta.toRingHom] (Fin 2 → K),
        Function.Injective L ∧ ∀ (a : K) (ha : sigma a = a) (v : Fin 2 → K),
          E (rankOneParameter sigma hsigma a ha v) =
            rankOneParameter sigma hsigma (theta a / alpha)
              (by rw [map_div₀, automorphism_fixed_of_commute sigma theta htheta a ha, halpha]) (L v) := by
  have hgamma0 : gamma ≠ 0 := by
    intro h
    have hh : alpha * beta = 0 := by simpa only [h, zero_mul] using hgamma.symm
    exact mul_ne_zero halpha0 hbeta0 hh
  have hsgamma0 : sigma gamma ≠ 0 := by
    intro h
    apply hgamma0
    apply sigma.injective
    simpa only [map_zero] using h
  have finish (theta : K ≃+* K) (htheta : Function.Commute sigma theta)
      (hS : ∀ (a : K) (ha : sigma a = a) (A : parameters sigma),
        E (fixedScaleHom sigma a ha A) = fixedScaleHom sigma (theta a)
          (automorphism_fixed_of_commute sigma theta htheta a ha) (E A))
      (hO : ∀ x, offDiagonalImageHom sigma hsigma E x = gamma * theta x) :
      ∃ L : (Fin 2 → K) →ₛₗ[theta.toRingHom] (Fin 2 → K),
        Function.Injective L ∧ ∀ (a : K) (ha : sigma a = a) (v : Fin 2 → K),
          E (rankOneParameter sigma hsigma a ha v) =
            rankOneParameter sigma hsigma (theta a / alpha)
              (by rw [map_div₀, automorphism_fixed_of_commute sigma theta htheta a ha, halpha]) (L v) := by
    refine ⟨twoCoordinateSemilinearMap theta alpha (sigma gamma),
      twoCoordinateSemilinearMap_injective theta alpha (sigma gamma) halpha0 hsgamma0, ?_⟩
    intro a ha v
    exact normalized_cone_rankOne_semilinear sigma theta hsigma htheta E hS hcone
      alpha beta gamma halpha hbeta halpha0 hbeta0 haxis0 haxis1 hgamma hO a ha v
  rcases hoff with hoff | hoff
  · obtain ⟨L, hL, hR⟩ := finish tau hcomm hscalar hoff
    exact ⟨tau, hcomm, L, hL, hR⟩
  · let theta : K ≃+* K := sigma.trans tau
    have htheta : Function.Commute sigma theta := by
      intro x
      exact hcomm (sigma x)
    have hS (a : K) (ha : sigma a = a) (A : parameters sigma) :
        E (fixedScaleHom sigma a ha A) = fixedScaleHom sigma (theta a)
          (automorphism_fixed_of_commute sigma theta htheta a ha) (E A) := by
      have he : theta a = tau a := congrArg tau ha
      simpa only [he] using hscalar a ha A
    obtain ⟨L, hL, hR⟩ := finish theta htheta hS hoff
    exact ⟨theta, htheta, L, hL, hR⟩

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
