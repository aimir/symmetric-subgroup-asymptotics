import SymmetricSubgroupAsymptotics.CFSGFFourOriginalGeneratedEquivalence
import SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorusAction

/-! The literal four-coordinate product torus and its signed scalar
action in the same original F4 Model. The construction pulls back the
proved generated-group homomorphism through the unconditional Model
equivalence, so no ordinary projective simplicity is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorus
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalGeneratedEquivalence CFSGFFourOriginalParameterizedTorus
open CFSGFFourOriginalMiddleWords CFSGFFourE6ProductTorus
open CFSGFFourE6ProductTorusAction CFSGFFourE6RelativeTorus
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourRelativeScalarIndex
open CFSGIntegerMatrixPowerHom CFSGE6GeckProductTorus
variable (K : Type) [Field K] [Finite K] [CharP K 2]

def modelProductTorusHom : (Fin 4→Kˣ)→*Model CartanMatrix.F₄ K :=
  (modelEquivGenerated K).symm.toMonoidHom.comp (productTorusGenerated K)

theorem modelEquivGenerated_product (x : Fin 4→Kˣ) :
    modelEquivGenerated K (modelProductTorusHom K x)=productTorusGenerated K x :=
  (modelEquivGenerated K).apply_symm_apply (productTorusGenerated K x)

theorem rawHom_modelProductTorus (x : Fin 4→Kˣ) :
    rawHom K (modelProductTorusHom K x)=rawProductTorus K (torusTuple K x) := by
  calc
    _=(modelEquivGenerated K (modelProductTorusHom K x)).val :=
      (modelEquivGenerated_val K _).symm
    _=(productTorusGenerated K x).val := congrArg Subtype.val (modelEquivGenerated_product K x)
    _=_ := productTorusGenerated_val K x

theorem modelProductTorus_word (x : Fin 4→Kˣ) :
    modelProductTorusHom K x=parameterTorus K 0 (x 0)*
      (parameterTorus K 1 (x 1)*(parameterTorus K 3 (x 3)*parameterTorus K 2 (x 2))) := by
  apply (modelEquivGenerated K).injective
  simp only [modelEquivGenerated_product,map_mul,modelEquivGenerated_parameterTorus]
  apply Subtype.ext
  change (productTorusGenerated K x).val=(torusWord K x).val
  rw [productTorusGenerated_val,torusWord_val]

theorem model_product_torus_action (x : Fin 4→Kˣ) (neg : Bool) (i : Fin 4) (a : K) :
    modelProductTorusHom K x*modelRoot CartanMatrix.F₄ K neg i a*(modelProductTorusHom K x)⁻¹=
      modelRoot CartanMatrix.F₄ K neg i
        (a*(if neg then (powerHom (G:=Kˣ) relativeCartan x i : K)⁻¹
          else (powerHom (G:=Kˣ) relativeCartan x i : K))) := by
  apply (modelEquivGenerated K).injective
  simp only [map_mul,map_inv,modelEquivGenerated_product,modelEquivGenerated_root]
  exact generated_product_torus_action K x neg i a

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorus
