import SymmetricSubgroupAsymptotics.BinaryPlaneQuartetFlatten
import SymmetricSubgroupAsymptotics.BinaryUntwistedQuartetPolynomial
import SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform

/-! The identity-local-factor companion to the cubic-twisted endpoint. -/
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryUntwistedQuartetNormalizedUniform
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneQuartetFlatten (flat)
open AlternatingFourBinaryActualPolynomialUniform (cycle)
abbrev Bit := ZMod 2
abbrev Space := Fin 4 → Plane

def permOperator (p : Equiv.Perm (Fin 4)) : Module.End Bit Space :=
  (LinearEquiv.funCongrLeft Bit Plane p.symm).toLinearMap

set_option maxHeartbeats 1000000 in
private theorem literal_operator :
    flat.conjRingEquiv
      (let A := permOperator cycle
       let T := permOperator AlternatingFourBinaryActualPolynomialUniform.flip
       let E := 1+A+A^2
       E*T*E+1+A^2)=BinaryUntwistedQuartetPolynomial.operator := by
  apply (Pi.basisFun Bit (Fin 8)).ext
  intro i
  funext j
  change flat
    ((let A := permOperator cycle
      let T := permOperator AlternatingFourBinaryActualPolynomialUniform.flip
      let E := 1+A+A^2
      E*T*E+1+A^2 : Module.End Bit Space) (flat.symm ((Pi.basisFun Bit (Fin 8)) i))) j=_
  simp only [Pi.basisFun_apply]
  revert i j
  decide +kernel

theorem uniform {H : Type} [Group H] (rho : Representation Bit H Space)
    (a t : H)
    (ha : ∀ v i, rho a v i=v (cycle⁻¹ i))
    (ht : ∀ v i, rho t v i=
      v (AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i)) :
    UniformSubrepresentationGeneratorBound rho 2 := by
  have hA : rho a=permOperator cycle := by
    apply LinearMap.ext
    intro v
    funext i
    exact ha v i
  have hT : rho t=permOperator AlternatingFourBinaryActualPolynomialUniform.flip := by
    apply LinearMap.ext
    intro v
    funext i
    exact ht v i
  let sigma : Representation Bit H (Fin 8 → Bit) :=
    flat.conjRingEquiv.toMonoidHom.comp rho
  let A : Bit[H] := MonoidAlgebra.single a 1
  let T : Bit[H] := MonoidAlgebra.single t 1
  let E := 1+A+A^2
  let w := E*T*E+1+A^2
  have hw : BinaryUntwistedQuartetPolynomial.operator=sigma.asAlgebraHom w := by
    have hconj : sigma.asAlgebraHom w=flat.conjRingEquiv (rho.asAlgebraHom w) := by
      simp [w,E,A,T,sigma]
    rw [hconj]
    dsimp only [w,E,A,T]
    simp only [map_add,map_mul,map_one,map_pow,Representation.asAlgebraHom_single_one]
    rw [hA,hT]
    simpa only [map_add,map_mul,map_one,map_pow] using literal_operator.symm
  have hu := BinaryUntwistedQuartetPolynomial.witness.uniform sigma w hw
  let inter : Representation.IntertwiningMap rho sigma := {
    toLinearMap := flat.toLinearMap
    isIntertwining' h := by
      apply LinearMap.ext
      intro v
      change flat (rho h v)=flat (rho h (flat.symm (flat v)))
      rw [flat.symm_apply_apply] }
  exact hu.of_injective inter flat.injective

end SymmetricSubgroupAsymptotics.BinaryUntwistedQuartetNormalizedUniform
