import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixMultivariateTransport
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCollectingTransport

/-! Exact two-parameter collecting transport through the actual
integer polynomials in two independent variables. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticParameterizedCollectingTransport
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticCollectingTransport
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

def parameterPositiveWord (K : Type*) [CommRing K] (i j : Fin r) (t a : K) :
    (Matrix I I K)ˣ :=
  canonicalRoot D K false i t*canonicalRoot D K false j a*
    (canonicalRoot D K false i t)⁻¹*(canonicalRoot D K false j a)⁻¹

theorem map_parameterPositiveWord_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (i j : Fin r) (t a : K) :
    f.mapMatrix (parameterPositiveWord D K i j t a : Matrix I I K)=
      (parameterPositiveWord D L i j (f t) (f a) : Matrix I I L) := by
  simp only [parameterPositiveWord,Units.val_mul,canonicalRoot_inverse,map_mul,
    map_canonicalRoot_val,map_neg]

theorem collecting_word_of_rational (K : Type*) [CommRing K] (i j : Fin r)
    (h : ∀t a : ℚ,parameterPositiveWord D ℚ i j t a=conjugateWord D ℚ i j (a*t))
    (t a : K) :
    parameterPositiveWord D K i j t a=conjugateWord D K i j (a*t) := by
  let M : Matrix I I (MvPolynomial (Fin 2) ℤ) :=
    parameterPositiveWord D (MvPolynomial (Fin 2) ℤ) i j (MvPolynomial.X 0) (MvPolynomial.X 1)
  let N : Matrix I I (MvPolynomial (Fin 2) ℤ) :=
    conjugateWord D (MvPolynomial (Fin 2) ℤ) i j (MvPolynomial.X 1*MvPolynomial.X 0)
  have hp : ∀b : Fin 2→ℚ,(MvPolynomial.eval₂Hom (Int.castRingHom ℚ) b).mapMatrix M=
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) b).mapMatrix N := by
    intro b
    dsimp only [M,N]
    simpa only [map_parameterPositiveWord_val,map_conjugateWord_val,map_mul,
      MvPolynomial.eval₂Hom_X'] using
      congrArg (fun u : (Matrix I I ℚ)ˣ=>(u : Matrix I I ℚ)) (h (b 0) (b 1))
  have hk := CFSGIntegerMatrixMultivariateTransport.evaluations_eq_of_rational_evaluations
    K M N hp ![t,a]
  apply Units.ext
  dsimp only [M,N] at hk
  simpa only [map_parameterPositiveWord_val,map_conjugateWord_val,map_mul,
    MvPolynomial.eval₂Hom_X',Matrix.cons_val_zero,Matrix.cons_val_one] using hk

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticParameterizedCollectingTransport
