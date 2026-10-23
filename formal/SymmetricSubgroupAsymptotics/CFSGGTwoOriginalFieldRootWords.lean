import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveRootWords
import SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram

/-! The actual identity-diagram field-tensor automorphism on the SAME
original Model fixes the literal Weyl words and acts on every one of the
six positive root parameters by that field automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFieldRootWords
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreModelRootGeneration
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoPositiveDirections
variable (K : Type) [Field K]
local notation "A" => CartanMatrix.G₂

def fieldModel (σ : K ≃+* K) : MulAut (Model A K) :=
  CFSGSerreFieldDiagram.modelAutomorphism A K (Equiv.refl (Fin 2)) (fun _ _ => rfl) σ

theorem fieldModel_root (σ : K ≃+* K) (neg : Bool) (i : Fin 2) (t : K) :
    fieldModel K σ (modelRoot A K neg i t)=modelRoot A K neg i (σ t) := by
  apply Subtype.ext
  change CFSGSerreFieldDiagram.ambientAutomorphism A K (Equiv.refl (Fin 2))
      (fun _ _ => rfl) σ (rootEquiv A K neg i t)=rootEquiv A K neg i (σ t)
  apply LinearEquiv.toLinearMap_injective
  exact CFSGSerreFieldDiagram.ambientAutomorphism_isRootElement A K
    (Equiv.refl (Fin 2)) (fun _ _ => rfl) σ neg i t _ (rootEquiv_isRootElement A K neg i t)

theorem fieldModel_shortWord (σ : K ≃+* K) : fieldModel K σ (shortWord K)=shortWord K := by
  simp only [shortWord,map_mul,fieldModel_root,map_one,map_neg]

theorem fieldModel_longWord (σ : K ≃+* K) : fieldModel K σ (longWord K)=longWord K := by
  simp only [longWord,map_mul,fieldModel_root,map_one,map_neg]

theorem fieldModel_directionModel (σ : K ≃+* K) (j : Fin 6) :
    fieldModel K σ (directionModel K j)=directionModel K j := by
  fin_cases j
  · exact map_one (fieldModel K σ)
  · exact map_one (fieldModel K σ)
  · exact fieldModel_longWord K σ
  · change fieldModel K σ (shortWord K * longWord K)=shortWord K * longWord K
    rw [map_mul,fieldModel_shortWord,fieldModel_longWord]
  · exact fieldModel_shortWord K σ
  · change fieldModel K σ (longWord K * shortWord K)=longWord K * shortWord K
    rw [map_mul,fieldModel_longWord,fieldModel_shortWord]

theorem fieldModel_positiveModel (σ : K ≃+* K) (j : Fin 6) (t : K) :
    fieldModel K σ (positiveModel K j t)=positiveModel K j (σ t) := by
  change fieldModel K σ (directionModel K j * modelRoot A K false (rootNode j) t *
      (directionModel K j)⁻¹)=
    directionModel K j * modelRoot A K false (rootNode j) (σ t) * (directionModel K j)⁻¹
  rw [map_mul,map_mul,map_inv,fieldModel_directionModel,fieldModel_root]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFieldRootWords
