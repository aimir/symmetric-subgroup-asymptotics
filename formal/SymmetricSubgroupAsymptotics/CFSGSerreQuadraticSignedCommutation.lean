import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingTransport

/-! Zero brackets between either signs of actual rational root operators
imply commutation of their integral parameter groups in every characteristic.
The integer word retains both independent parameters and both signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSignedCommutation
open CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

def signedWord (K : Type*) [CommRing K] (e f : Bool) (i j : Fin r) (t a : K) :
    (Matrix I I K)ˣ :=
  canonicalRoot D K e i t*canonicalRoot D K f j a*
    (canonicalRoot D K e i t)⁻¹*(canonicalRoot D K f j a)⁻¹

theorem rational_word (e f : Bool) (i j : Fin r)
    (h : ⁅fieldRoot D ℚ e i,fieldRoot D ℚ f j⁆=0) (t a : ℚ) :
    signedWord D ℚ e f i j t a=1 := by
  have he : (canonicalRoot D ℚ e i t : Matrix I I ℚ)*fieldRoot D ℚ f j*
      (((canonicalRoot D ℚ e i t)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=
      fieldRoot D ℚ f j := by
    have hh := canonicalRoot_conjugation_of_double_lie D e i
      (fieldRoot D ℚ f j) (by rw [h,lie_zero]) t
    simpa only [h,smul_zero,add_zero] using hh
  have hp := CFSGUnitConjugationPolynomial.conjugate_quadratic
    (canonicalRoot D ℚ e i t) (fieldRoot D ℚ f j) (fieldRoot D ℚ f j) he a
  have hv := canonicalRoot_val_rational D f j a
  have hr : canonicalRoot D ℚ e i t*canonicalRoot D ℚ f j a*
      (canonicalRoot D ℚ e i t)⁻¹=canonicalRoot D ℚ f j a := by
    apply Units.ext
    simpa only [Units.val_mul,hv] using hp
  change (canonicalRoot D ℚ e i t*canonicalRoot D ℚ f j a*
    (canonicalRoot D ℚ e i t)⁻¹)*(canonicalRoot D ℚ f j a)⁻¹=1
  rw [hr,mul_inv_cancel]

theorem map_signedWord {K L : Type*} [CommRing K] [CommRing L]
    (g : K→+*L) (e f : Bool) (i j : Fin r) (t a : K) :
    g.mapMatrix (signedWord D K e f i j t a : Matrix I I K)=
      (signedWord D L e f i j (g t) (g a) : Matrix I I L) := by
  simp only [signedWord,Units.val_mul,canonicalRoot_inverse,map_mul,
    map_canonicalRoot_val,map_neg]

theorem roots_commute (K : Type*) [CommRing K] (e f : Bool) (i j : Fin r)
    (h : ⁅fieldRoot D ℚ e i,fieldRoot D ℚ f j⁆=0) (t a : K) :
    Commute (canonicalRoot D K e i t) (canonicalRoot D K f j a) := by
  let M : Matrix I I (MvPolynomial (Fin 2) ℤ) :=
    signedWord D (MvPolynomial (Fin 2) ℤ) e f i j (MvPolynomial.X 0) (MvPolynomial.X 1)
  have hp : ∀b : Fin 2→ℚ,(MvPolynomial.eval₂Hom (Int.castRingHom ℚ) b).mapMatrix M=
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) b).mapMatrix (1 : Matrix I I (MvPolynomial (Fin 2) ℤ)) := by
    intro b
    dsimp only [M]
    simpa only [map_signedWord,MvPolynomial.eval₂Hom_X',map_one,Units.val_one] using
      congrArg (fun u : (Matrix I I ℚ)ˣ=>(u : Matrix I I ℚ))
        (rational_word D e f i j h (b 0) (b 1))
  have hk := CFSGIntegerMatrixMultivariateTransport.evaluations_eq_of_rational_evaluations K M 1 hp ![t,a]
  have he : signedWord D K e f i j t a=1 := by
    apply Units.ext
    dsimp only [M] at hk
    simpa only [map_signedWord,MvPolynomial.eval₂Hom_X',map_one,Units.val_one,
      Matrix.cons_val_zero,Matrix.cons_val_one] using hk
  change canonicalRoot D K e i t*canonicalRoot D K f j a=
    canonicalRoot D K f j a*canonicalRoot D K e i t
  have hh := congrArg (fun u : (Matrix I I K)ˣ=>u*canonicalRoot D K f j a*
    canonicalRoot D K e i t) he
  dsimp only [signedWord] at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one,one_mul] using hh

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSignedCommutation
