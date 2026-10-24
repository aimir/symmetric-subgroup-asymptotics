import SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorus
import SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarInjective

/-! Literal parameter and product-torus coordinate injectivity in the
original characteristic-two F4 Model. The integral inverse of the actual
relative Cartan scalar map recovers all four torus coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorusInjective
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalProductTorus CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckRelativeRootGenerated CFSGE6GeckRelativeSimpleHom
open CFSGE6GeckSignedSimpleParameters CFSGFFourRelativeScalarIndex
open CFSGIntegerMatrixPowerHom
variable (K : Type) [Field K] [Finite K] [CharP K 2]

private theorem rawOrbit_id (neg : Bool) (i : Fin 4) (t : K) :
    rawOrbitHom K (RingEquiv.refl K) neg i (Multiplicative.ofAdd t)=
      orbitParameter K neg i t := by
  fin_cases i <;> rfl

private theorem rawOrbit_injective (neg : Bool) (i : Fin 4) :
    Function.Injective (rawOrbitHom K (RingEquiv.refl K) neg i) := by
  fin_cases i
  · exact rawPaired_injective K (RingEquiv.refl K) neg 0
  · exact rawPaired_injective K (RingEquiv.refl K) neg 1
  · exact rawSingleton_injective K neg 1
  · exact rawSingleton_injective K neg 0

theorem modelRoot_parameter_injective (neg : Bool) (i : Fin 4) :
    Function.Injective (modelRoot CartanMatrix.F₄ K neg i) := by
  intro a b he
  have h := congrArg (rawHom K) he
  simp only [rawHom_root,CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter] at h
  have hraw : rawOrbitHom K (RingEquiv.refl K) neg i (Multiplicative.ofAdd a)=
      rawOrbitHom K (RingEquiv.refl K) neg i (Multiplicative.ofAdd b) := by
    simpa only [rawOrbit_id] using h
  exact congrArg Multiplicative.toAdd (rawOrbit_injective K neg i hraw)

theorem modelProductTorusHom_injective : Function.Injective (modelProductTorusHom K) := by
  intro x y he
  apply CFSGFFourRelativeScalarInjective.powerHom_injective (G:=Kˣ)
  funext i
  have hx := model_product_torus_action K x false i 1
  have hy := model_product_torus_action K y false i 1
  rw [he] at hx
  have h := modelRoot_parameter_injective K false i (hx.symm.trans hy)
  apply Units.ext
  simpa only [Bool.false_eq_true,if_false,one_mul] using h

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorusInjective
