import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedActionImage
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedProjectiveImage
import SymmetricSubgroupAsymptotics.CFSGQuadraticConjugationImageParity
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNoncentralMatrix
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylUnits
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalTransport

/-! Uniform parity for the ORIGINAL triality model in every field.
Both signed central-node root actions have actual ORIGINAL derived
preimages by the proved fixed-root-generated action containment. Their
Weyl word is a fourth root and is noncentral in that SAME derived action
image. Its full-centre quotient is even, and the already proved original
projective equivalence transports parity using inherited simplicity only.
No root census, numerical evaluation, standard-model identification,
finite/order input, or characteristic restriction occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialitySelectedWeylEvenOrder
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckDerivedRootGeneration
open CFSGTrialityGeckGeneratedActionImage CFSGTrialityGeckDerivedProjectiveImage
open CFSGTrialityTripleFixedRoots CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

theorem root_action_mem_derived (q : CFSG.PrimePower) (neg : Bool) :
    matrixAction (q.Extension 3) (canonicalElementaryRoot rawData (q.Extension 3) neg 1 1) ∈
      (derivedImageAction q).range := by
  let g : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
    ⟨canonicalRoot rawData (q.Extension 3) neg 1 1,
      central_root_mem_generated (q.Extension 3) (definingFieldAutomorphism q 3)
        neg 1 (map_one _)⟩
  have h : generatedAction (q.Extension 3) (definingFieldAutomorphism q 3) g ∈
      (derivedImageAction q).range :=
    generated_action_range_le_original_derived q ⟨g,rfl⟩
  change matrixAction (q.Extension 3)
    (canonicalElementaryRoot rawData (q.Extension 3) neg 1 1) ∈ _ at h
  exact h

def rootLift (q : CFSG.PrimePower) (neg : Bool) : commutator (Fixed q) :=
  Classical.choose (root_action_mem_derived q neg)

theorem rootLift_image (q : CFSG.PrimePower) (neg : Bool) :
    derivedImageAction q (rootLift q neg) =
      matrixAction (q.Extension 3) (canonicalElementaryRoot rawData (q.Extension 3) neg 1 1) :=
  Classical.choose_spec (root_action_mem_derived q neg)

def derivedWeyl (q : CFSG.PrimePower) : commutator (Fixed q) :=
  rootLift q false * (rootLift q true)⁻¹ * rootLift q false

private theorem elementaryRoot_inverse (K : Type) [Field K] (neg : Bool) (t : K) :
    (canonicalElementaryRoot rawData K neg 1 t)⁻¹ =
      canonicalElementaryRoot rawData K neg 1 (-t) := by
  apply Subtype.ext
  exact canonicalRoot_inverse rawData K neg 1 t

theorem derivedWeyl_image (q : CFSG.PrimePower) :
    derivedImageAction q (derivedWeyl q) =
      matrixAction (q.Extension 3) (matrixRankOneWord (q.Extension 3) 1) := by
  calc
    _ = matrixAction (q.Extension 3)
        (canonicalElementaryRoot rawData (q.Extension 3) false 1 1 *
          (canonicalElementaryRoot rawData (q.Extension 3) true 1 1)⁻¹ *
          canonicalElementaryRoot rawData (q.Extension 3) false 1 1) := by
      simp only [derivedWeyl,map_mul,map_inv,rootLift_image]
    _ = _ := by
      rw [elementaryRoot_inverse]
      rfl

theorem derivedWeyl_action (q : CFSG.PrimePower) (y : Image (q.Extension 3)) :
    (derivedImageAction q (derivedWeyl q) y).val =
      (canonicalWeyl data (q.Extension 3) 1 : Matrix GeckIndex GeckIndex (q.Extension 3)) *
        y.val * (↑((canonicalWeyl data (q.Extension 3) 1)⁻¹) :
          Matrix GeckIndex GeckIndex (q.Extension 3)) := by
  rw [derivedWeyl_image,matrixAction_apply]
  change (canonicalWeyl rawData (q.Extension 3) 1 : Matrix GeckIndex GeckIndex (q.Extension 3)) *
    y.val * (↑((canonicalWeyl rawData (q.Extension 3) 1)⁻¹) :
      Matrix GeckIndex GeckIndex (q.Extension 3)) = _
  simp only [data,canonicalWeyl_transportSource]

theorem derivedRoot_action (q : CFSG.PrimePower) (y : Image (q.Extension 3)) :
    (derivedImageAction q (rootLift q false) y).val =
      (canonicalRoot data (q.Extension 3) false 1 1 : Matrix GeckIndex GeckIndex (q.Extension 3)) *
        y.val * (↑((canonicalRoot data (q.Extension 3) false 1 1)⁻¹) :
          Matrix GeckIndex GeckIndex (q.Extension 3)) := by
  rw [rootLift_image,matrixAction_apply]
  change (canonicalRoot rawData (q.Extension 3) false 1 1 : Matrix GeckIndex GeckIndex (q.Extension 3)) *
    y.val * (↑((canonicalRoot rawData (q.Extension 3) false 1 1)⁻¹) :
      Matrix GeckIndex GeckIndex (q.Extension 3)) = _
  simp only [data,canonicalRoot_transportSource]

theorem weyl_four (q : CFSG.PrimePower) : (canonicalWeyl data (q.Extension 3) 1)^4=1 := by
  rw [data,canonicalWeyl_transportSource]
  exact CFSGNormTwoGeckWeylUnits.weyl_four (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index (q.Extension 3) 1

theorem weyl_root_noncommuting (q : CFSG.PrimePower) :
    (canonicalRoot data (q.Extension 3) false 1 1 : Matrix GeckIndex GeckIndex (q.Extension 3)) *
      ((canonicalWeyl data (q.Extension 3) 1 : Matrix GeckIndex GeckIndex (q.Extension 3)) *
        fieldRoot data (q.Extension 3) false 1 *
        (↑((canonicalWeyl data (q.Extension 3) 1)⁻¹) : Matrix GeckIndex GeckIndex (q.Extension 3))) *
      (↑((canonicalRoot data (q.Extension 3) false 1 1)⁻¹) : Matrix GeckIndex GeckIndex (q.Extension 3)) ≠
    (canonicalWeyl data (q.Extension 3) 1 : Matrix GeckIndex GeckIndex (q.Extension 3)) *
      fieldRoot data (q.Extension 3) false 1 *
      (↑((canonicalWeyl data (q.Extension 3) 1)⁻¹) : Matrix GeckIndex GeckIndex (q.Extension 3)) := by
  simpa only [data,canonicalRoot_transportSource,canonicalWeyl_transportSource,
    fieldRoot_transportSource] using
      CFSGNormTwoGeckNoncentralMatrix.root_does_not_fix_weyl_root
        (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
        Base Index (q.Extension 3) 1

theorem triality_even_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : Even (Nat.card (CFSG.Models.TrialityD4 q)) := by
  rw [Nat.card_congr (originalProjectiveImageEquiv q).toEquiv]
  exact CFSGQuadraticConjugationImageParity.image_projective_even_card data (q.Extension 3)
    (derivedImageAction q) (derivedWeyl q) (rootLift q false) 1
    (derivedWeyl_action q) (derivedRoot_action q) (weyl_four q) (weyl_root_noncommuting q)

end SymmetricSubgroupAsymptotics.CFSGTrialitySelectedWeylEvenOrder
