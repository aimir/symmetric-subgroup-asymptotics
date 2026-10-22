import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylWord
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticOrthogonalCollecting

/-! Root-line conjugation by an actual integral Weyl word. Rational
coefficient recognition is transported as a parameter-polynomial
identity, so no division is performed after reduction of characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWordRootTransport
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

def rootWord (K : Type*) [CommRing K] (w : List (Fin r)) (neg : Bool) (i : Fin r) (a : K) :
    (Matrix I I K)ˣ := canonicalWord D K w*canonicalRoot D K neg i a*(canonicalWord D K w)⁻¹

theorem rational_scaled_root (u : (Matrix I I ℚ)ˣ) (neg neg' : Bool) (i j : Fin r)
    (c : ℚ) (hc : (u : Matrix I I ℚ)*fieldRoot D ℚ neg i*
      ((u⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=c • fieldRoot D ℚ neg' j) (a : ℚ) :
    u*canonicalRoot D ℚ neg i a*u⁻¹=canonicalRoot D ℚ neg' j (c*a) := by
  apply Units.ext
  simp only [Units.val_mul,canonicalRoot_val_rational]
  calc
    _=1+a • (c • fieldRoot D ℚ neg' j)+(a^2/2) • (c • fieldRoot D ℚ neg' j)^2 :=
      CFSGUnitConjugationPolynomial.conjugate_quadratic u
        (fieldRoot D ℚ neg i) (c • fieldRoot D ℚ neg' j) hc a
    _=_ := by
      simp only [pow_two,smul_mul_assoc,mul_smul_comm,smul_smul]
      module

theorem map_rootWord_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (w : List (Fin r)) (neg : Bool) (i : Fin r) (a : K) :
    f.mapMatrix (rootWord D K w neg i a : Matrix I I K)=
      (rootWord D L w neg i (f a) : Matrix I I L) := by
  simp only [rootWord,Units.val_mul,map_mul,map_word_val,map_word_inv_val,map_canonicalRoot_val]

theorem word_root_of_rational (K : Type*) [CommRing K] (w : List (Fin r))
    (neg neg' : Bool) (i j : Fin r) (ε : ℤ)
    (h : ∀a : ℚ,rootWord D ℚ w neg i a=canonicalRoot D ℚ neg' j ((ε:ℚ)*a)) (a : K) :
    rootWord D K w neg i a=canonicalRoot D K neg' j ((ε:K)*a) := by
  let M : Matrix I I (Polynomial ℤ) := rootWord D (Polynomial ℤ) w neg i Polynomial.X
  let N : Matrix I I (Polynomial ℤ) :=
    canonicalRoot D (Polynomial ℤ) neg' j ((ε:Polynomial ℤ)*Polynomial.X)
  have hp : ∀c : ℚ,(Polynomial.eval₂RingHom (Int.castRingHom ℚ) c).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom ℚ) c).mapMatrix N := by
    intro c
    dsimp only [M,N]
    simpa only [map_rootWord_val,map_canonicalRoot_val,map_mul,map_intCast,
      Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using
      congrArg (fun u : (Matrix I I ℚ)ˣ=>(u : Matrix I I ℚ)) (h c)
  have hk := CFSGIntegerMatrixPolynomialTransport.evaluations_eq_of_rational_evaluations K M N hp a
  apply Units.ext
  dsimp only [M,N] at hk
  simpa only [map_rootWord_val,map_canonicalRoot_val,map_mul,map_intCast,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using hk

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWordRootTransport
