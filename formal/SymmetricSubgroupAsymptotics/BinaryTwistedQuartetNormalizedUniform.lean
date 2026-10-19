import SymmetricSubgroupAsymptotics.BinaryPlaneQuartetFlatten
import SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform

/-! Uniform two for an actual normalized cubic-twisted quartet action.
The two operators are identified before invoking the literal certificate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetNormalizedUniform
open BinaryPlanePermutationAffineEquiv
open BinaryTwistedQuartetPolynomial (Bit cubic)
open BinaryPlaneQuartetFlatten (flat)
open AlternatingFourBinaryActualPolynomialUniform (cycle)
abbrev Space := Fin 4 → Plane

def localCubic : Module.End Bit Plane where
  toFun := cubic
  map_add' u v := by
    ext i
    fin_cases i <;> simp [cubic,add_assoc,add_left_comm,add_comm]
  map_smul' a u := by
    ext i
    fin_cases i <;> simp [cubic,mul_add]

def cycleOperator : Module.End Bit Space :=
  LinearMap.pi (fun i => localCubic.comp (LinearMap.proj (cycle⁻¹ i)))

def flipOperator : Module.End Bit Space :=
  (LinearEquiv.funCongrLeft Bit Plane
    AlternatingFourBinaryActualPolynomialUniform.flip.symm).toLinearMap

set_option maxHeartbeats 1000000 in
private theorem literal_sum :
    flat.conjRingEquiv (cycleOperator+flipOperator)=
      BinaryTwistedQuartetPolynomial.operator := by
  apply (Pi.basisFun Bit (Fin 8)).ext
  intro i
  funext j
  change flat ((cycleOperator+flipOperator)
    (flat.symm ((Pi.basisFun Bit (Fin 8)) i))) j=_
  simp only [Pi.basisFun_apply]
  revert i j
  decide +kernel

theorem uniform {H : Type} [Group H] (rho : Representation Bit H Space)
    (a t : H)
    (ha : ∀ v i, rho a v i=cubic (v (cycle⁻¹ i)))
    (ht : ∀ v i, rho t v i=
      v (AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i)) :
    UniformSubrepresentationGeneratorBound rho 2 := by
  have hA : rho a=cycleOperator := by
    apply LinearMap.ext
    intro v
    funext i
    exact ha v i
  have hT : rho t=flipOperator := by
    apply LinearMap.ext
    intro v
    funext i
    exact ht v i
  let sigma : Representation Bit H (Fin 8 → Bit) :=
    flat.conjRingEquiv.toMonoidHom.comp rho
  have hs : sigma a+sigma t=BinaryTwistedQuartetPolynomial.operator := by
    change flat.conjRingEquiv (rho a)+flat.conjRingEquiv (rho t)=_
    rw [← map_add,hA,hT]
    exact literal_sum
  have hu := BinaryTwistedQuartetActualUniform.uniform sigma a t
    (fun v i => congrArg (fun f : Module.End Bit (Fin 8 → Bit) => f v i) hs)
  let inter : Representation.IntertwiningMap rho sigma := {
    toLinearMap := flat.toLinearMap
    isIntertwining' h := by
      apply LinearMap.ext
      intro v
      change flat (rho h v)=flat (rho h (flat.symm (flat v)))
      rw [flat.symm_apply_apply] }
  exact hu.of_injective inter flat.injective

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetNormalizedUniform
