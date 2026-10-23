import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalNaturalEquivalence
import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveDirections

/-! Literal six positive root words in the SAME original Model and their
exact native images. The two Weyl orientations are deliberately retained:
short uses (+1,-1,+1), long uses (-1,+1,-1). No higher-root sign or
exceptional covariance is inferred from an unsigned root permutation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveRootWords
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections CFSGGTwoShortWeylMatrices
open CFSGGTwoOriginalNaturalEquivalence
variable (K : Type) [Field K]
local notation "A" => CartanMatrix.G₂

def shortWord : Model A K :=
  modelRoot A K false 0 1 * modelRoot A K true 0 (-1) * modelRoot A K false 0 1

def longWord : Model A K :=
  modelRoot A K false 1 (-1) * modelRoot A K true 1 1 * modelRoot A K false 1 (-1)

def directionModel (j : Fin 6) : Model A K :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => longWord K
  | 3 => shortWord K * longWord K
  | 4 => shortWord K
  | _ => longWord K * shortWord K

def positiveModel (j : Fin 6) (t : K) : Model A K :=
  directionModel K j * modelRoot A K false (rootNode j) t * (directionModel K j)⁻¹

theorem shortWord_native : modelEquivNatural K (shortWord K)=naturalShortWeyl K := by
  simp only [shortWord,naturalShortWeyl,map_mul,modelEquivNatural_root]

theorem longWord_native : modelEquivNatural K (longWord K)=naturalLongWeyl K := by
  simp only [longWord,naturalLongWeyl,map_mul,modelEquivNatural_root]

theorem directionModel_native (j : Fin 6) :
    (modelEquivNatural K (directionModel K j)).val=directionWord K j := by
  fin_cases j
  · exact congrArg Subtype.val (map_one (modelEquivNatural K))
  · exact congrArg Subtype.val (map_one (modelEquivNatural K))
  · exact congrArg Subtype.val (longWord_native K)
  · change (modelEquivNatural K (shortWord K * longWord K)).val=shortWeyl K * longWeyl K
    simpa only [shortWord_native,longWord_native] using
      congrArg (fun u : naturalGroup K => u.val)
        (map_mul (modelEquivNatural K) (shortWord K) (longWord K))
  · exact congrArg Subtype.val (shortWord_native K)
  · change (modelEquivNatural K (longWord K * shortWord K)).val=longWeyl K * shortWeyl K
    simpa only [shortWord_native,longWord_native] using
      congrArg (fun u : naturalGroup K => u.val)
        (map_mul (modelEquivNatural K) (longWord K) (shortWord K))

theorem positiveModel_native (j : Fin 6) (t : K) :
    modelEquivNatural K (positiveModel K j t)=⟨positiveRoot K j t,positiveRoot_mem K j t⟩ := by
  apply Subtype.ext
  simp only [positiveModel,map_mul,map_inv]
  change (modelEquivNatural K (directionModel K j)).val *
      (modelEquivNatural K (modelRoot A K false (rootNode j) t)).val *
      ((modelEquivNatural K (directionModel K j)).val)⁻¹=
    directionWord K j * rootTransvection K false (rootNode j) t * (directionWord K j)⁻¹
  rw [modelEquivNatural_root,directionModel_native]
  rfl

theorem modelRoot_inv (neg : Bool) (i : Fin 2) (t : K) :
    (modelRoot A K neg i t)⁻¹=modelRoot A K neg i (-t) := by
  apply (modelEquivNatural K).injective
  rw [map_inv,modelEquivNatural_root,modelEquivNatural_root]
  apply Subtype.ext
  apply Units.ext
  change (↑((rootTransvection K neg i t)⁻¹):Mat K)=
    (rootTransvection K neg i (-t):Mat K)
  rw [rootTransvection_inv_val,rootTransvection_val]
  simp only [neg_smul,neg_sq,sub_eq_add_neg]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveRootWords
