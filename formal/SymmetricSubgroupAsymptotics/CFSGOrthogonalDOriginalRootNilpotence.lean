import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntrinsicEquivalence
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroLieRealization
import SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint

/-! Uniform original-source root nilpotence, proved integrally BEFORE
reduction and therefore valid in characteristic two. Injection here is
only over Z into the literal integer matrices; no modular ambient
faithfulness is inferred. -/
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootNilpotence
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDOriginalRootCandidates
variable (r : ℕ) (hr : 4 ≤ r)

theorem integralRepresentation_injective : Function.Injective (integralOrthogonalRepresentation r hr) := by
  intro x y h
  apply CFSGOrthogonalDOriginalIntrinsicEquivalence.realization_injective r hr
  exact Subtype.ext h

include hr in
theorem integralOperator_large (neg : Bool) (i : Fin r) (k : ℕ) (hk : 3 ≤ k) :
    integralOperator (CartanMatrix.D r) neg i k=0 := by
  apply LinearMap.ext
  intro x
  apply integralRepresentation_injective r hr
  rw [CFSGSerreSquareZeroMatrix.integralRepresentation_operator (realizationData r hr),
    CFSGIntegralSquareZeroOperators.operator_large ℤ _ _ k hk]
  simp only [LinearMap.zero_apply,map_zero]

include hr in
theorem baseChange_integralOperator_large (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin r) (k : ℕ) (hk : 3 ≤ k) :
    (integralOperator (CartanMatrix.D r) neg i k).baseChange K=0 := by
  rw [integralOperator_large r hr neg i k hk,LinearMap.baseChange_zero]

def rootSource (neg : Bool) (i : Fin r) : Source r:=
  latticeGenerator (CartanMatrix.D r) (if neg then .F i else .E i)

theorem rootSource_image (neg : Bool) (i : Fin r) :
    integralOrthogonalRepresentation r hr (rootSource r neg i)=rootMatrix ℤ r neg i := by
  cases neg
  · exact CFSGOrthogonalDOriginalIntegralAction.generator_image r hr (.E i)
  · exact CFSGOrthogonalDOriginalIntegralAction.generator_image r hr (.F i)

include hr in
theorem integral_triple_bracket (neg : Bool) (i : Fin r) (x : Source r) :
    ⁅rootSource r neg i,⁅rootSource r neg i,⁅rootSource r neg i,x⁆⁆⁆=0 := by
  apply integralRepresentation_injective r hr
  simp only [CFSGSerreSquareZeroLieRealization.integralRepresentation_map_lie (realizationData r hr),
    rootSource_image,map_zero]
  exact CFSGSquareZeroAdjoint.lie_lie_lie _ _ (rootMatrix_sq_zero ℤ r neg i)

include hr in
theorem space_triple_bracket (K : Type) [Field K] (neg : Bool) (i : Fin r)
    (x : Space (CartanMatrix.D r) K) :
    ⁅(1 : K) ⊗ₜ[ℤ] rootSource r neg i,
      ⁅(1 : K) ⊗ₜ[ℤ] rootSource r neg i,⁅(1 : K) ⊗ₜ[ℤ] rootSource r neg i,x⁆⁆⁆=0 := by
  let u : Space (CartanMatrix.D r) K := (1 : K) ⊗ₜ[ℤ] rootSource r neg i
  let ad : Space (CartanMatrix.D r) K →+ Space (CartanMatrix.D r) K :=
    AddMonoidHom.mk' (fun y => ⁅u,y⁆) (LieRing.lie_add u)
  let triple := ad.comp (ad.comp ad)
  change triple x = 0
  induction x using TensorProduct.induction_on with
  | zero => exact triple.map_zero
  | tmul a x =>
    change ⁅(1 : K) ⊗ₜ[ℤ] rootSource r neg i,
      ⁅(1 : K) ⊗ₜ[ℤ] rootSource r neg i,
        ⁅(1 : K) ⊗ₜ[ℤ] rootSource r neg i,a ⊗ₜ[ℤ] x⁆⁆⁆=0
    simp only [CFSGSerreIntegralLieAlgebra.spaceBracket_tmul,one_mul,
      integral_triple_bracket r hr,TensorProduct.tmul_zero]
  | add x y hx hy => rw [triple.map_add,hx,hy,add_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootNilpotence
