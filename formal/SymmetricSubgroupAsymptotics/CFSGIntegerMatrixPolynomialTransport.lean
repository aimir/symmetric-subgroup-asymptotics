import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.CharZero.Infinite

/-! Exact parameter-polynomial transport. Equality at EVERY rational
parameter first proves equality of the actual integer polynomials, then
evaluation is valid in every coefficient ring, including bad primes.
There is no finite sampling or unproved denominator cancellation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPolynomialTransport
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrix_eq_of_rational_evaluations (M N : Matrix I I (Polynomial ℤ))
    (h : ∀a : ℚ,(Polynomial.eval₂RingHom (Int.castRingHom ℚ) a).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom ℚ) a).mapMatrix N) : M=N := by
  apply Matrix.ext
  intro i j
  apply Polynomial.map_injective (f:=Int.castRingHom ℚ)
    (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  apply Polynomial.funext
  intro a
  have he := congrArg (fun A : Matrix I I ℚ=>A i j) (h a)
  change Polynomial.eval₂ (Int.castRingHom ℚ) a (M i j)=
    Polynomial.eval₂ (Int.castRingHom ℚ) a (N i j) at he
  simpa only [Polynomial.eval_map] using he

theorem evaluations_eq_of_rational_evaluations (K : Type*) [CommRing K]
    (M N : Matrix I I (Polynomial ℤ))
    (h : ∀a : ℚ,(Polynomial.eval₂RingHom (Int.castRingHom ℚ) a).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom ℚ) a).mapMatrix N) (a : K) :
    (Polynomial.eval₂RingHom (Int.castRingHom K) a).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom K) a).mapMatrix N :=
  congrArg (Polynomial.eval₂RingHom (Int.castRingHom K) a).mapMatrix
    (matrix_eq_of_rational_evaluations M N h)

end SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPolynomialTransport
