import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticParameterizedCollectingTransport
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRationalRootValues
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootConjugation
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial

/-! Commuting positive root WORDS, transported through the exact
two-parameter integer polynomials, rather than division after reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingTransport
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticParameterizedCollectingTransport
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem rational_commuting_word (i j : Fin r)
    (hE : ⁅fieldRoot D ℚ false i,fieldRoot D ℚ false j⁆=0) (t a : ℚ) :
    parameterPositiveWord D ℚ i j t a=1 := by
  have hfix : (canonicalRoot D ℚ false i t : Matrix I I ℚ)*fieldRoot D ℚ false j*
      (((canonicalRoot D ℚ false i t)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=
      fieldRoot D ℚ false j := by
    have hh := canonicalRoot_conjugation_of_double_lie D false i
      (fieldRoot D ℚ false j) (by rw [hE,lie_zero]) t
    simpa only [hE,smul_zero,add_zero] using hh
  have hpoly := CFSGUnitConjugationPolynomial.conjugate_quadratic
    (canonicalRoot D ℚ false i t) (fieldRoot D ℚ false j)
    (fieldRoot D ℚ false j) hfix a
  have ha := canonicalRoot_val_rational D false j a
  have hroot : canonicalRoot D ℚ false i t*canonicalRoot D ℚ false j a*
      (canonicalRoot D ℚ false i t)⁻¹=canonicalRoot D ℚ false j a := by
    apply Units.ext
    simpa only [Units.val_mul,ha] using hpoly
  change (canonicalRoot D ℚ false i t*canonicalRoot D ℚ false j a*
    (canonicalRoot D ℚ false i t)⁻¹)*(canonicalRoot D ℚ false j a)⁻¹=1
  rw [hroot,mul_inv_cancel]

theorem commuting_word_of_rational (K : Type*) [CommRing K] (i j : Fin r)
    (h : ∀t a : ℚ,parameterPositiveWord D ℚ i j t a=1) (t a : K) :
    parameterPositiveWord D K i j t a=1 := by
  let M : Matrix I I (MvPolynomial (Fin 2) ℤ) :=
    parameterPositiveWord D (MvPolynomial (Fin 2) ℤ) i j (MvPolynomial.X 0) (MvPolynomial.X 1)
  have hp : ∀b : Fin 2→ℚ,(MvPolynomial.eval₂Hom (Int.castRingHom ℚ) b).mapMatrix M=
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) b).mapMatrix (1 : Matrix I I (MvPolynomial (Fin 2) ℤ)) := by
    intro b
    dsimp only [M]
    simpa only [map_parameterPositiveWord_val,MvPolynomial.eval₂Hom_X',map_one,
      Units.val_one] using
      congrArg (fun u : (Matrix I I ℚ)ˣ=>(u : Matrix I I ℚ)) (h (b 0) (b 1))
  have hk := CFSGIntegerMatrixMultivariateTransport.evaluations_eq_of_rational_evaluations
    K M 1 hp ![t,a]
  apply Units.ext
  dsimp only [M] at hk
  simpa only [map_parameterPositiveWord_val,MvPolynomial.eval₂Hom_X',map_one,
    Matrix.cons_val_zero,Matrix.cons_val_one,Units.val_one] using hk

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingTransport
