import SymmetricSubgroupAsymptotics.BinaryLocalAlternatingFourPolynomial
import Mathlib.GroupTheory.Perm.Fin

/-! Bind actual acting elements to the existing literal cyclic operator.
Only operator identities are inputs; no generator-capacity premise. -/
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform
abbrev Scalar := ZMod 2

abbrev Vector := Fin 4 → Scalar

def cycle : Equiv.Perm (Fin 4) := Equiv.swap 1 2*Equiv.swap 2 3
def flip : Equiv.Perm (Fin 4) := Equiv.swap 0 3*Equiv.swap 1 2

def permOperator (p : Equiv.Perm (Fin 4)) : Module.End Scalar Vector :=
  (LinearEquiv.funCongrLeft Scalar Scalar p.symm).toLinearMap

private theorem literal_operator :
    BinaryLocalAlternatingFourPolynomial.operator Scalar =
      let A := permOperator cycle
      let T := permOperator flip
      let E := 1+A+A^2
      E*T*E+1+A^2 := by
  apply (Pi.basisFun Scalar (Fin 4)).ext
  intro i
  simp only [Pi.basisFun_apply]
  funext j
  revert i j
  decide +kernel

/-- The same explicit polynomial operator works whenever the actual
representation contains these literal normalized permutation operators. -/
theorem uniform {H : Type} [Group H] (rho : Representation Scalar H Vector)
    (a t : H)
    (ha : ∀ v i, rho a v i=v (cycle⁻¹ i))
    (ht : ∀ v i, rho t v i=v (flip⁻¹ i)) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  let A : Scalar[H] := MonoidAlgebra.single a 1
  let T : Scalar[H] := MonoidAlgebra.single t 1
  let E := 1+A+A^2
  let w := E*T*E+1+A^2
  have hA : rho a=permOperator cycle := by
    apply LinearMap.ext
    intro v
    funext i
    exact ha v i
  have hT : rho t=permOperator flip := by
    apply LinearMap.ext
    intro v
    funext i
    exact ht v i
  apply BinaryLocalAlternatingFourPolynomial.binaryWitness.uniform rho w
  dsimp only [w,E,A,T]
  simp only [map_add,map_mul,map_one,map_pow,Representation.asAlgebraHom_single_one]
  rw [hA,hT]
  exact literal_operator

end SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform
