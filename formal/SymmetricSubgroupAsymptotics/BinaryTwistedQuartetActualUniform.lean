import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetPolynomial

/-! Transfer the literal cubic-twist certificate to two actual acting
elements. The input records their actual operator sum, not a capacity. -/
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualUniform
open BinaryTwistedQuartetPolynomial (Bit Vector operator)

theorem uniform {H : Type} [Group H] (rho : Representation Bit H Vector)
    (a t : H) (hact : ∀ v i, rho a v i+rho t v i=operator v i) :
    UniformSubrepresentationGeneratorBound rho 2 := by
  let w : Bit[H] := MonoidAlgebra.single a 1+MonoidAlgebra.single t 1
  apply BinaryTwistedQuartetPolynomial.witness.uniform rho w
  dsimp only [w]
  simp only [map_add,Representation.asAlgebraHom_single_one]
  apply LinearMap.ext
  intro v
  funext i
  exact (hact v i).symm

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualUniform
