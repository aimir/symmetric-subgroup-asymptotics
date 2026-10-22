import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylString
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRationalRootValues
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCollectingTransport

/-! Orthogonal simple-root collecting on the actual quadratic units.
The rational calculation is transported as an integer polynomial word,
so the final identity does not require division in the coefficient ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticOrthogonalCollecting
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticAdjointWeylString
open CFSGSerreQuadraticCollectingTransport
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem weyl_fixes_of_lie_zero (i : Fin r) (X : Matrix I I ℚ)
    (hE : ⁅fieldRoot D ℚ false i,X⁆=0)
    (hF : ⁅fieldRoot D ℚ true i,X⁆=0) :
    (canonicalWeyl D ℚ i : Matrix I I ℚ)*X*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=X := by
  have hU (a : ℚ) : operator D false i a X=X := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D false i X
      (by rw [hE,lie_zero]) a
    simpa only [hE,smul_zero,add_zero] using hh
  have hV (a : ℚ) : operator D true i a X=X := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D true i X
      (by rw [hF,lie_zero]) a
    simpa only [hF,smul_zero,add_zero] using hh
  change CFSGAlgebraConjugationAction.action ℚ (Matrix I I ℚ)
    (canonicalWeyl D ℚ i) X=X
  rw [canonicalWeyl,map_mul,map_mul]
  change operator D false i 1 (operator D true i (-1) (operator D false i 1 X))=X
  rw [hU,hV,hU]

theorem rational_root_word (i j : Fin r)
    (hE : ⁅fieldRoot D ℚ false i,fieldRoot D ℚ false j⁆=0)
    (hF : ⁅fieldRoot D ℚ true i,fieldRoot D ℚ false j⁆=0) (a : ℚ) :
    conjugateWord D ℚ i j a=canonicalRoot D ℚ false j a := by
  apply Units.ext
  change (canonicalWeyl D ℚ i : Matrix I I ℚ)*
    (canonicalRoot D ℚ false j a : Matrix I I ℚ)*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=_
  simp only [canonicalRoot_val_rational]
  exact CFSGUnitConjugationPolynomial.conjugate_quadratic (canonicalWeyl D ℚ i)
    (fieldRoot D ℚ false j) (fieldRoot D ℚ false j)
    (weyl_fixes_of_lie_zero D i _ hE hF) a

theorem root_word_of_rational (K : Type*) [CommRing K] (i j : Fin r)
    (h : ∀a : ℚ,conjugateWord D ℚ i j a=canonicalRoot D ℚ false j a) (a : K) :
    conjugateWord D K i j a=canonicalRoot D K false j a := by
  let M : Matrix I I (Polynomial ℤ) := conjugateWord D (Polynomial ℤ) i j Polynomial.X
  let N : Matrix I I (Polynomial ℤ) := canonicalRoot D (Polynomial ℤ) false j Polynomial.X
  have hp : ∀b : ℚ,(Polynomial.eval₂RingHom (Int.castRingHom ℚ) b).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom ℚ) b).mapMatrix N := by
    intro b
    dsimp only [M,N]
    simpa only [map_conjugateWord_val,map_canonicalRoot_val,
      Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using
      congrArg (fun u : (Matrix I I ℚ)ˣ=>(u : Matrix I I ℚ)) (h b)
  have hk := CFSGIntegerMatrixPolynomialTransport.evaluations_eq_of_rational_evaluations K M N hp a
  apply Units.ext
  dsimp only [M,N] at hk
  simpa only [map_conjugateWord_val,map_canonicalRoot_val,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using hk

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticOrthogonalCollecting
