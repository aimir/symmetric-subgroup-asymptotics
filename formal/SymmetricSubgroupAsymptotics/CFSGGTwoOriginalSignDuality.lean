import SymmetricSubgroupAsymptotics.CFSGMatrixUnitInverseTranspose
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalNaturalEquivalence
import SymmetricSubgroupAsymptotics.CFSGGTwoWeylMonomial
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveRootWords

/-! Actual sign-duality of the whole original G2 Model, transported from
inverse-transpose on the independently proved faithful natural image.
Both literal simple Weyl words are fixed. This does not use ordinary G2
simplicity, a projective lifting assertion, or a root-system recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSignDuality
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGGTwoSerreMatrices
open CFSGGTwoOriginalNaturalEquivalence CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoWeylMonomial CFSGGTwoShortWeylMatrices CFSGGTwoPositiveDirections
open CFSGMatrixUnitInverseTranspose
variable (K : Type) [Field K]
local notation "A" => CartanMatrix.G₂

theorem inverseTranspose_root (neg : Bool) (i : Fin 2) (t : K) :
    inverseTranspose (rootTransvection K neg i t)=rootTransvection K (!neg) i (-t) := by
  apply Units.ext
  change ((rootTransvection K neg i t)⁻¹).val.transpose=
    (rootTransvection K (!neg) i (-t)).val
  rw [rootTransvection_inv_val,rootTransvection_val]
  cases neg <;> simp only [rootMatrix,rootSecond,Bool.false_eq_true,if_false,if_true,
    Bool.not_false,Bool.not_true,negative,negativeSecond,Matrix.transpose_add,
    Matrix.transpose_neg,Matrix.transpose_smul,Matrix.transpose_one,
    Matrix.transpose_transpose,neg_smul,neg_sq,sub_eq_add_neg]

def rawDual : Model A K→*(Mat K)ˣ :=
  inverseTranspose.comp ((naturalGroup K).subtype.comp (modelEquivNatural K).toMonoidHom)

theorem rawDual_apply (g : Model A K) :
    rawDual K g=inverseTranspose (modelEquivNatural K g).val := rfl

theorem rawDual_root (neg : Bool) (i : Fin 2) (t : K) :
    rawDual K (modelRoot A K neg i t)=rootTransvection K (!neg) i (-t) := by
  rw [rawDual_apply,modelEquivNatural_root]
  exact inverseTranspose_root K neg i t

private theorem rawDual_range_le : (rawDual K).range≤naturalGroup K := by
  apply CFSGGeneratedActionRange.range_le_of_generators (rootSet A K)
    (rootSet_generate A K) (rawDual K) (naturalGroup K)
  rintro _ ⟨neg,i,t,rfl⟩
  rw [rawDual_root]
  exact (naturalRoot K (!neg) i (-t)).property

def nativeDual : Model A K→*naturalGroup K :=
  (rawDual K).codRestrict (naturalGroup K) (fun g=>rawDual_range_le K ⟨g,rfl⟩)

def modelDual : Model A K→*Model A K :=
  (modelEquivNatural K).symm.toMonoidHom.comp (nativeDual K)

theorem modelDual_native (g : Model A K) :
    (modelEquivNatural K (modelDual K g)).val=
      inverseTranspose (modelEquivNatural K g).val := by
  change ((modelEquivNatural K) ((modelEquivNatural K).symm (nativeDual K g))).val=_
  rw [(modelEquivNatural K).apply_symm_apply]
  rfl

theorem modelDual_root (neg : Bool) (i : Fin 2) (t : K) :
    modelDual K (modelRoot A K neg i t)=modelRoot A K (!neg) i (-t) := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  rw [modelDual_native,modelEquivNatural_root,modelEquivNatural_root]
  exact inverseTranspose_root K neg i t

theorem modelDual_involutive : Function.Involutive (modelDual K) := by
  intro g
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  rw [modelDual_native,modelDual_native,inverseTranspose_involutive]

def signDual : MulAut (Model A K) where
  toFun := modelDual K
  invFun := modelDual K
  left_inv := modelDual_involutive K
  right_inv := modelDual_involutive K
  map_mul' := map_mul (modelDual K)

theorem signDual_root (neg : Bool) (i : Fin 2) (t : K) :
    signDual K (modelRoot A K neg i t)=modelRoot A K (!neg) i (-t) :=
  modelDual_root K neg i t

theorem signDual_shortWord : signDual K (shortWord K)=shortWord K := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  change (modelEquivNatural K (modelDual K (shortWord K))).val=_
  rw [modelDual_native,shortWord_native]
  change inverseTranspose (shortWeyl K)=shortWeyl K
  apply inverseTranspose_monomial _ shortPermutation (shortWeight K)
    (shortWeyl_monomial K)
  intro i
  unfold shortWeight
  split_ifs <;> simp

theorem signDual_longWord : signDual K (longWord K)=longWord K := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  change (modelEquivNatural K (modelDual K (longWord K))).val=_
  rw [modelDual_native,longWord_native]
  change inverseTranspose (longWeyl K)=longWeyl K
  apply inverseTranspose_monomial _ longPermutation (longWeight K)
    (longWeyl_monomial K)
  intro i
  unfold longWeight
  split_ifs <;> simp

theorem signDual_direction (j : Fin 6) :
    signDual K (directionModel K j)=directionModel K j := by
  fin_cases j <;> simp only [directionModel,map_one,map_mul,
    signDual_shortWord,signDual_longWord]

/-- Twelve actual signed root words, with identical Weyl directions. -/
def signedModel (neg : Bool) (j : Fin 6) (t : K) : Model A K :=
  directionModel K j*modelRoot A K neg (rootNode j) t*(directionModel K j)⁻¹

theorem signedModel_positive (j : Fin 6) (t : K) :
    signedModel K false j t=positiveModel K j t := rfl

theorem signDual_signedModel (neg : Bool) (j : Fin 6) (t : K) :
    signDual K (signedModel K neg j t)=signedModel K (!neg) j (-t) := by
  simp only [signedModel,map_mul,map_inv,signDual_direction,signDual_root]

theorem negative_as_dual (j : Fin 6) (t : K) :
    signedModel K true j t=signDual K (positiveModel K j (-t)) := by
  change signedModel K true j t=signDual K (signedModel K false j (-t))
  rw [signDual_signedModel]
  simp only [Bool.not_false,neg_neg]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSignDuality
