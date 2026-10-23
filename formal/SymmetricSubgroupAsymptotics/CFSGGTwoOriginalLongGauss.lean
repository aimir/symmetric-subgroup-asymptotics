import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRankTwoTorus

/-! A literal long-axis rank-one Gauss identity in the whole original
Model. The only computation is the checked sparse long action on eight
coordinates, with two nonzero unit parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalLongGauss
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGGTwoSerreMatrices
open CFSGGTwoOriginalRankTwoTorus CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoLongTorusAction

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 2=c := rfl
private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 3=d := rfl

variable (K : Type) [Field K]

private theorem naturalRoot_val (s : Bool) (t : K) :
    ((naturalRoot K s 1 t).val:Mat K)=(rootTransvection K s 1 t:Mat K) := rfl

theorem long_native_gauss (c a : Kˣ) :
    longWeylParameter c * naturalRoot K false 1 (a:K) =
      naturalRoot K false 1 (-(c:K)^2*(a⁻¹:Kˣ)) * longTorus (-c*a⁻¹) *
        naturalRoot K true 1 (a⁻¹:Kˣ) := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  simp only [Subgroup.coe_mul,Units.val_mul,←Matrix.mulVec_mulVec,naturalRoot_val]
  rw [positive_apply,longWeylParameter_apply,negative_apply,longTorus_apply,positive_apply]
  funext x
  rcases x with i|i <;> fin_cases i <;>
    simp [positiveAction,negativeAction,torusAction,weylAction,pos,neg,vec4_two,vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> ring

theorem longParameter_native (c : Kˣ) :
    modelEquivNatural K (weylParameter K 1 c)=longWeylParameter c := by
  simp only [weylParameter,map_mul,modelEquivNatural_root,longWeylParameter]

theorem longParameter_gauss (c a : Kˣ) :
    weylParameter K 1 c * modelRoot CartanMatrix.G₂ K false 1 (a:K) =
      modelRoot CartanMatrix.G₂ K false 1 (-(c:K)^2*(a⁻¹:Kˣ)) *
        torusNode K 1 (-c*a⁻¹) * modelRoot CartanMatrix.G₂ K true 1 (a⁻¹:Kˣ) := by
  apply (modelEquivNatural K).injective
  simpa only [map_mul,longParameter_native,longNode_native,modelEquivNatural_root] using
    long_native_gauss K c a

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalLongGauss
