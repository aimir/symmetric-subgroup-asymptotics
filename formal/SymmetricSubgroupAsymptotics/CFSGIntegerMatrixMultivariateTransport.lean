import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.CharZero.Infinite

/-! Exact transport of matrix identities in ANY finite or infinite
family of integer polynomial parameters. The premise is evaluation at
every rational assignment; equality of integer polynomials is proved
before evaluation in an arbitrary coefficient ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIntegerMatrixMultivariateTransport
variable {I σ : Type*} [Fintype I] [DecidableEq I]

theorem matrix_eq_of_rational_evaluations (M N : Matrix I I (MvPolynomial σ ℤ))
    (h : ∀a : σ→ℚ,(MvPolynomial.eval₂Hom (Int.castRingHom ℚ) a).mapMatrix M=
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) a).mapMatrix N) : M=N := by
  apply Matrix.ext
  intro i j
  apply MvPolynomial.map_injective (f:=Int.castRingHom ℚ)
    (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  apply MvPolynomial.funext
  intro a
  have he := congrArg (fun B : Matrix I I ℚ=>B i j) (h a)
  change MvPolynomial.eval₂ (Int.castRingHom ℚ) a (M i j)=
    MvPolynomial.eval₂ (Int.castRingHom ℚ) a (N i j) at he
  simpa only [MvPolynomial.eval_map] using he

theorem evaluations_eq_of_rational_evaluations (K : Type*) [CommRing K]
    (M N : Matrix I I (MvPolynomial σ ℤ))
    (h : ∀a : σ→ℚ,(MvPolynomial.eval₂Hom (Int.castRingHom ℚ) a).mapMatrix M=
      (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) a).mapMatrix N) (a : σ→K) :
    (MvPolynomial.eval₂Hom (Int.castRingHom K) a).mapMatrix M=
      (MvPolynomial.eval₂Hom (Int.castRingHom K) a).mapMatrix N :=
  congrArg (MvPolynomial.eval₂Hom (Int.castRingHom K) a).mapMatrix
    (matrix_eq_of_rational_evaluations M N h)

end SymmetricSubgroupAsymptotics.CFSGIntegerMatrixMultivariateTransport
