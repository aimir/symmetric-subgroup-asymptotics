import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedTorusConjugation

/-! The SAME literal six-node product torus acts on both signs, with
inverse Cartan scalar on the negative canonical simple root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusSigned
open CFSGE6GeckProductTorus CFSGProductTorusAction CFSGIntegerMatrixPowerHom
open CFSGNormTwoCoordinateSignedTorusConjugation CFSGIntegerMatrixPairing
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGTwistedE6GeckDiagramCovariance
open CFSGNormTwoGeckTorusHom CFSGE6GeckSignedSimpleParameters CFSGSerreQuadraticMatrix

private theorem simple_pairing (i j : Fin 6) :
    integerPairing CartanMatrix.E₆ (E6Index i : Roots CartanMatrix.E₆).val
      (E6Index j : Roots CartanMatrix.E₆).val=CartanMatrix.E₆ j i := by
  change integerPairing CartanMatrix.E₆ (Pi.single i 1) (Pi.single j 1)=CartanMatrix.E₆ j i
  simp only [integerPairing,Matrix.toBilin'_single]
  exact (congrArg (fun M : Matrix (Fin 6) (Fin 6) ℤ => M i j) CartanMatrix.E₆_transpose).symm

theorem rawProductTorus_negative_action (K : Type) [Field K] (x : Fin 6→Kˣ) (j : Fin 6) (a : K) :
    rawProductTorus K x*canonicalRoot rawData K true j a*(rawProductTorus K x)⁻¹=
      canonicalRoot rawData K true j (a*(powerHom (G := Kˣ) CartanMatrix.E₆ x j : K)⁻¹) := by
  have he := product_action (simpleTorusHom K) (simple_tori_commute K) (-CartanMatrix.E₆)
    (rawSimpleHom K true) (by
      intro i t k b
      change parameterTorusHom CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
          E6Base E6Index K i t*canonicalRoot rawData K true k b*
        (parameterTorusHom CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
          E6Base E6Index K i t)⁻¹=_
      rw [parameterTorusHom_apply]
      have hsigned := torus_conjugate_negative
        CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K i k t b
      change CFSGNormTwoGeckParameterizedTorus.parameterTorus CartanMatrix.E₆
          CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K i t *
          canonicalRoot rawData K true k b *
          (CFSGNormTwoGeckParameterizedTorus.parameterTorus CartanMatrix.E₆
            CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K i t)⁻¹ =
        canonicalRoot rawData K true k
          (b*(t : K)^(-integerPairing CartanMatrix.E₆
            (E6Index i : Roots CartanMatrix.E₆).val
            (E6Index k : Roots CartanMatrix.E₆).val)) at hsigned
      rw [simple_pairing] at hsigned
      exact hsigned) x j a
  have hpow : powerHom (G := Kˣ) (-CartanMatrix.E₆) x j=(powerHom (G := Kˣ) CartanMatrix.E₆ x j)⁻¹ := by
    simp only [powerHom_apply,Matrix.neg_apply,zpow_neg,Finset.prod_inv_distrib]
  simpa only [hpow,Units.val_inv_eq_inv_val] using he

theorem rawProductTorus_signed_action (K : Type) [Field K] (x : Fin 6→Kˣ)
    (neg : Bool) (j : Fin 6) (a : K) :
    rawProductTorus K x*canonicalRoot rawData K neg j a*(rawProductTorus K x)⁻¹=
      canonicalRoot rawData K neg j (a*(if neg then (powerHom (G := Kˣ) CartanMatrix.E₆ x j : K)⁻¹
        else (powerHom (G := Kˣ) CartanMatrix.E₆ x j : K))) := by
  cases neg
  · exact rawProductTorus_simple_action K x j a
  · exact rawProductTorus_negative_action K x j a

end SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusSigned
