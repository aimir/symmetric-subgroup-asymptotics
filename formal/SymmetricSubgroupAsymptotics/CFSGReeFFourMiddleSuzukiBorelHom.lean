import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleScalarSurjectivity
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusGroup
import SymmetricSubgroupAsymptotics.CFSGSuzukiBorelSemidirectHom
import SymmetricSubgroupAsymptotics.CFSGSuzukiCentralAnnihilatorIndex

/-! The actual Suzuki unipotent middle chart and an inverse-scalar
slice of the genuine Ree torus give a semidirect-product homomorphism
into the SAME original Ree F4 group. Only the central source must be
faithful; no whole Levi identification or Suzuki simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiBorelHom
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalMiddleTorusAction
open CFSGReeFFourMiddleScalarSurjectivity CFSGReeFFourFixedMiddleTorusAction
open CFSGReeFFourFixedTorusGroup CFSGReeFFourPerfectProjection
open CFSGSuzukiUnipotent CFSGSuzukiCentralExtensionLayers

def inverseScalarHom (m : ℕ) : (Field m)ˣ →* (Field m)ˣ where
  toFun c := scalarInverse m c⁻¹
  map_one' := by simp only [inv_one,scalarInverse,map_one,mul_one]
  map_mul' c d := by
    simp only [mul_inv_rev,scalarInverse,map_mul]
    ac_rfl

def torusHom (m : ℕ) (hm : 0 < m) : (Field m)ˣ →* CFSG.Models.ReeF4 m :=
  (fixedToOriginal m hm).comp ((middleTorusHom m).comp (inverseScalarHom m))

theorem torus_conjugation (m : ℕ) (hm : 0 < m) (c : (Field m)ˣ)
    (u : unipotentSubgroup m) :
    originalMiddleEmbedding m hm (torusAutHom m c u)=
      torusHom m hm c*originalMiddleEmbedding m hm u*(torusHom m hm c)⁻¹ := by
  have h := original_fixed_torus_middle_action m hm 1 (inverseScalarHom m c) u
  have hs : middleScalar m 1 (inverseScalarHom m c)=c⁻¹ := middleScalar_inverse m c⁻¹
  rw [hs,inv_inv] at h
  exact h

def extensionHom (m : ℕ) (hm : 0 < m) :
    CFSGSuzukiCentralAnnihilatorIndex.Borel m →* CFSG.Models.ReeF4 m :=
  SemidirectProduct.lift (originalMiddleEmbedding m hm) (torusHom m hm)
    (fun c => MonoidHom.ext (fun u => torus_conjugation m hm c u))

theorem extensionHom_inl (m : ℕ) (hm : 0 < m) (u : unipotentSubgroup m) :
    extensionHom m hm (SemidirectProduct.inl u)=originalMiddleEmbedding m hm u := by
  simp only [extensionHom,SemidirectProduct.lift_inl]

theorem extensionHom_central_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (fun c : Multiplicative (Field m) =>
      extensionHom m hm (SemidirectProduct.inl (centralHom m c))) := by
  intro c d h
  dsimp only at h
  rw [extensionHom_inl,extensionHom_inl] at h
  exact centralHom_injective m (originalMiddleEmbedding_injective m hm h)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiBorelHom
