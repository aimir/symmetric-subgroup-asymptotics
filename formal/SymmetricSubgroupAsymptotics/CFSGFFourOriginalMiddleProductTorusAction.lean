import SymmetricSubgroupAsymptotics.CFSGFFourOriginalProductTorus
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleProductTorusAction

/-! The two higher middle words in the SAME original F4 Model have the
expected product-torus weights. This uses the unconditional faithful
original-model embedding, not ordinary projective simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleProductTorusAction
open CFSGFFourOriginalProductTorus CFSGFFourOriginalMiddleWords
open CFSGFFourE6ProductTorus CFSGFFourRelativeScalarIndex CFSGIntegerMatrixPowerHom
open CFSGE6GeckMiddleProductTorusAction
variable (K : Type) [Field K] [Finite K] [CharP K 2]

private theorem middle_raw_scalars (x : Fin 4 → Kˣ) :
    powerHom CartanMatrix.E₆ (torusTuple K x) 2=powerHom relativeCartan x 1 ∧
    powerHom CartanMatrix.E₆ (torusTuple K x) 3=powerHom relativeCartan x 2 ∧
    powerHom CartanMatrix.E₆ (torusTuple K x) 4=powerHom relativeCartan x 1 :=
  ⟨congrFun (powerHom_torusTuple K x) 2,
    congrFun (powerHom_torusTuple K x) 3,congrFun (powerHom_torusTuple K x) 4⟩

theorem model_product_torus_middleLong (x : Fin 4 → Kˣ) (a : K) :
    modelProductTorusHom K x*middleLong K a*(modelProductTorusHom K x)⁻¹=
      middleLong K (a*((powerHom relativeCartan x 1)^2*powerHom relativeCartan x 2 : Kˣ)) := by
  apply rawHom_injective K
  simp only [map_mul,map_inv,rawHom_modelProductTorus,rawHom_middleLong]
  obtain ⟨h2,h3,h4⟩ := middle_raw_scalars K x
  have h := product_torus_highestMiddle K (torusTuple K x) a
  rw [h2,h3,h4] at h
  have he : (powerHom relativeCartan x 1*powerHom relativeCartan x 2)*
      powerHom relativeCartan x 1=(powerHom relativeCartan x 1)^2*powerHom relativeCartan x 2 := by
    rw [pow_two]
    ac_rfl
  rw [he] at h
  exact h

theorem model_product_torus_middleShort (x : Fin 4 → Kˣ) (a : K) :
    modelProductTorusHom K x*middleShort K a*(modelProductTorusHom K x)⁻¹=
      middleShort K (a*(powerHom relativeCartan x 1*powerHom relativeCartan x 2 : Kˣ)) := by
  apply rawHom_injective K
  simp only [map_mul,map_inv,rawHom_modelProductTorus,rawHom_middleShort]
  obtain ⟨h2,h3,h4⟩ := middle_raw_scalars K x
  have h := product_torus_middlePair K (torusTuple K x) (h2.trans h4.symm) a
  rw [h2,h3] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleProductTorusAction
