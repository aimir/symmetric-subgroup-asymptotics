import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWordRootTransport

/-! Exact comparison of two literal Weyl-word root parametrizations.
Rational coefficient-line equality gives the parameter change, and an
integral parameter change transports to every commutative coefficient
ring without dividing in the target characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWordRootComparison
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGSerreQuadraticWordRootTransport
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem rational_scaled_pair (u v : (Matrix I I ℚ)ˣ) (neg neg' : Bool) (i j : Fin r)
    (c : ℚ) (hc : (u : Matrix I I ℚ)*fieldRoot D ℚ neg i*
      ((u⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=
        c • ((v : Matrix I I ℚ)*fieldRoot D ℚ neg' j*
          ((v⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ))) (a : ℚ) :
    u*canonicalRoot D ℚ neg i a*u⁻¹=
      v*canonicalRoot D ℚ neg' j (c*a)*v⁻¹ := by
  let Y : Matrix I I ℚ := (v : Matrix I I ℚ)*fieldRoot D ℚ neg' j*
    ((v⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)
  have hl := CFSGUnitConjugationPolynomial.conjugate_quadratic u
    (fieldRoot D ℚ neg i) (c • Y) hc a
  have hr := CFSGUnitConjugationPolynomial.conjugate_quadratic v
    (fieldRoot D ℚ neg' j) Y rfl (c*a)
  apply Units.ext
  simp only [Units.val_mul,canonicalRoot_val_rational]
  rw [hl,hr]
  simp only [pow_two,smul_mul_assoc,mul_smul_comm,smul_smul]
  module

theorem word_pair_of_rational (K : Type*) [CommRing K] (w v : List (Fin r))
    (neg neg' : Bool) (i j : Fin r) (ε : ℤ)
    (h : ∀a : ℚ,rootWord D ℚ w neg i a=rootWord D ℚ v neg' j ((ε:ℚ)*a)) (a : K) :
    rootWord D K w neg i a=rootWord D K v neg' j ((ε:K)*a) := by
  let M : Matrix I I (Polynomial ℤ) := rootWord D (Polynomial ℤ) w neg i Polynomial.X
  let N : Matrix I I (Polynomial ℤ) :=
    rootWord D (Polynomial ℤ) v neg' j ((ε:Polynomial ℤ)*Polynomial.X)
  have hp : ∀c : ℚ,(Polynomial.eval₂RingHom (Int.castRingHom ℚ) c).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom ℚ) c).mapMatrix N := by
    intro c
    dsimp only [M,N]
    simpa only [map_rootWord_val,map_mul,map_intCast,
      Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using
      congrArg (fun u : (Matrix I I ℚ)ˣ=>(u : Matrix I I ℚ)) (h c)
  have hk := CFSGIntegerMatrixPolynomialTransport.evaluations_eq_of_rational_evaluations K M N hp a
  apply Units.ext
  dsimp only [M,N] at hk
  simpa only [map_rootWord_val,map_mul,map_intCast,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using hk

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWordRootComparison
