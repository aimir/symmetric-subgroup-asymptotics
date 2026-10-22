import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPolynomialTransport
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylConjugationTransport

/-! Exact integer PARAMETER-word transport of adjacent positive
collecting. The words themselves are evaluated over ℤ[X]; equality at
all rational parameters proves their integer polynomial identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCollectingTransport
open CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

def positiveWord (K : Type*) [CommRing K] (i j : Fin r) (a : K) : (Matrix I I K)ˣ :=
  canonicalRoot D K false i 1*canonicalRoot D K false j a*
    (canonicalRoot D K false i 1)⁻¹*(canonicalRoot D K false j a)⁻¹

def conjugateWord (K : Type*) [CommRing K] (i j : Fin r) (a : K) : (Matrix I I K)ˣ :=
  canonicalWeyl D K i*canonicalRoot D K false j a*(canonicalWeyl D K i)⁻¹

theorem map_positiveWord_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (i j : Fin r) (a : K) :
    f.mapMatrix (positiveWord D K i j a : Matrix I I K)=
      (positiveWord D L i j (f a) : Matrix I I L) := by
  simp only [positiveWord,Units.val_mul,canonicalRoot_inverse,map_mul,
    map_canonicalRoot_val,map_one,map_neg]

theorem map_conjugateWord_val {K L : Type*} [CommRing K] [CommRing L]
    (f : K→+*L) (i j : Fin r) (a : K) :
    f.mapMatrix (conjugateWord D K i j a : Matrix I I K)=
      (conjugateWord D L i j (f a) : Matrix I I L) := by
  simp only [conjugateWord,Units.val_mul,map_mul,map_canonicalWeyl_val,
    map_canonicalRoot_val,map_canonicalWeyl_inv_val]

theorem collecting_word_of_rational (K : Type*) [CommRing K] (i j : Fin r)
    (h : ∀a : ℚ,positiveWord D ℚ i j a=conjugateWord D ℚ i j a) (a : K) :
    positiveWord D K i j a=conjugateWord D K i j a := by
  let M : Matrix I I (Polynomial ℤ) := positiveWord D (Polynomial ℤ) i j Polynomial.X
  let N : Matrix I I (Polynomial ℤ) := conjugateWord D (Polynomial ℤ) i j Polynomial.X
  have hp : ∀b : ℚ,(Polynomial.eval₂RingHom (Int.castRingHom ℚ) b).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom ℚ) b).mapMatrix N := by
    intro b
    dsimp only [M,N]
    simpa only [map_positiveWord_val,map_conjugateWord_val,
      Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using
      congrArg (fun u : (Matrix I I ℚ)ˣ=>(u : Matrix I I ℚ)) (h b)
  have hk := CFSGIntegerMatrixPolynomialTransport.evaluations_eq_of_rational_evaluations K M N hp a
  apply Units.ext
  dsimp only [M,N] at hk
  simpa only [map_positiveWord_val,map_conjugateWord_val,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using hk

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCollectingTransport
