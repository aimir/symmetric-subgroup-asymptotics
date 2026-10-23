import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceWordAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionQuotientCoordinates

/-! Literal ORIGINAL fixed-subgroup witnesses for every displayed natural
section, with equality of their actions on the same original integral
image.  Membership in the derived fixed subgroup is not asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFixedSections
open CFSGSerreFixedRootElements CFSGTrialityTripleFixedRoots CFSGTrialityFixedWeylWords
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckSectionRootLabels
open CFSGTrialityGeckSectionQuotientCoordinates CFSGSerreQuadraticMatrix
open CFSGTrialityGeckWordCoordinateTwist CFSGSerreOrdinaryTwists

def fixedImageAction (q : CFSG.PrimePower) :
    Fixed q →* (Image (q.Extension 3) ≃ₗ[q.Extension 3] Image (q.Extension 3)) :=
  (imageRepresentation data (q.Extension 3)).comp
    (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality (fun _ => q.order))

def sourceShortTransport (q : CFSG.PrimePower) (s : Fin 3) : Fixed q :=
  ![1,CFSGTrialityFixedWeylWords.longWeyl q,
    CFSGTrialityFixedWeylWords.shortWeyl q * CFSGTrialityFixedWeylWords.longWeyl q] s

def sourceLongTransport (q : CFSG.PrimePower) (s : Fin 3) : Fixed q :=
  ![1,CFSGTrialityFixedWeylWords.shortWeyl q,
    CFSGTrialityFixedWeylWords.longWeyl q * CFSGTrialityFixedWeylWords.shortWeyl q] s

def sourceShortSection (q : CFSG.PrimePower) (s : Fin 3) (neg : Bool) (t : q.Extension 3) :
    Fixed q :=
  sourceShortTransport q s * orbitRoot q neg t * (sourceShortTransport q s)⁻¹

def sourceLongSection (q : CFSG.PrimePower) (s : Fin 3) (neg : Bool) (t : q.Extension 3)
    (ht : t^q.order = t) : Fixed q :=
  sourceLongTransport q s * CFSGTrialityFixedWeylWords.longRoot q neg t ht *
    (sourceLongTransport q s)⁻¹

theorem sourceShortTransport_toModel (q : CFSG.PrimePower) (s : Fin 3) :
    fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality (fun _ => q.order)
      (sourceShortTransport q s) = sourceWord (q.Extension 3) (shortWord s) := by
  fin_cases s <;>
    simp [sourceShortTransport,shortWord,sourceWord,sourceRankOneWord,rankOneWord,
      shortWeyl_toModel,longWeyl_toModel,mul_assoc]

theorem sourceLongTransport_toModel (q : CFSG.PrimePower) (s : Fin 3) :
    fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality (fun _ => q.order)
      (sourceLongTransport q s) = sourceWord (q.Extension 3) (longWord s) := by
  fin_cases s <;>
    simp [sourceLongTransport,longWord,sourceWord,sourceRankOneWord,rankOneWord,
      shortWeyl_toModel,longWeyl_toModel,mul_assoc]

def matrixShortOrbit (K : Type) [Field K] (σ : K ≃+* K) (neg : Bool) (t : K) : MatrixGroup K :=
  canonicalElementaryRoot rawData K neg 0 t * canonicalElementaryRoot rawData K neg 2 (σ t) *
    canonicalElementaryRoot rawData K neg 3 (σ (σ t))

def matrixShortSection (K : Type) [Field K] (σ : K ≃+* K)
    (s : Fin 3) (neg : Bool) (t : K) : MatrixGroup K :=
  matrixWord K (shortWord s) * matrixShortOrbit K σ neg t * (matrixWord K (shortWord s))⁻¹

def matrixLongSection (K : Type) [Field K] (s : Fin 3) (neg : Bool) (t : K) : MatrixGroup K :=
  matrixWord K (longWord s) * canonicalElementaryRoot rawData K neg 1 t *
    (matrixWord K (longWord s))⁻¹

theorem matrixShortSection_val (K : Type) [Field K] (σ : K ≃+* K)
    (s : Fin 3) (neg : Bool) (t : K) :
    (matrixShortSection K σ s neg t).val = shortSection K σ s neg t := by
  simp only [matrixShortSection,Subgroup.coe_mul,Subgroup.coe_inv,matrixWord_val,
    shortSection,shortTransport_word]
  rfl

theorem matrixLongSection_val (K : Type) [Field K] (s : Fin 3) (neg : Bool) (t : K) :
    (matrixLongSection K s neg t).val = longSection K s neg t := by
  simp only [matrixLongSection,Subgroup.coe_mul,Subgroup.coe_inv,matrixWord_val,
    longSection,longTransport_word]
  rfl

theorem sourceShortSection_action (q : CFSG.PrimePower) (s : Fin 3) (neg : Bool)
    (t : q.Extension 3) :
    fixedImageAction q (sourceShortSection q s neg t) =
      matrixAction (q.Extension 3)
        (matrixShortSection (q.Extension 3) (definingFieldAutomorphism q 3) s neg t) := by
  have horbit : fixedImageAction q (orbitRoot q neg t) =
      matrixAction (q.Extension 3)
        (matrixShortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) neg t) := by
    change imageRepresentation data (q.Extension 3)
      (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
        (fun _ => q.order) (orbitRoot q neg t)) = _
    rw [orbitRoot_toModel]
    simp only [map_mul,source_root_action,matrixShortOrbit,definingFieldAutomorphism_apply]
  change imageRepresentation data (q.Extension 3)
    (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (sourceShortSection q s neg t)) = _
  simp only [sourceShortSection,map_mul,map_inv,sourceShortTransport_toModel,word_action]
  change matrixAction (q.Extension 3) (matrixWord (q.Extension 3) (shortWord s)) *
      fixedImageAction q (orbitRoot q neg t) *
      (matrixAction (q.Extension 3) (matrixWord (q.Extension 3) (shortWord s)))⁻¹ = _
  rw [horbit]
  simp only [matrixShortSection,map_mul,map_inv]

theorem sourceLongSection_action (q : CFSG.PrimePower) (s : Fin 3) (neg : Bool)
    (t : q.Extension 3) (ht : t^q.order = t) :
    fixedImageAction q (sourceLongSection q s neg t ht) =
      matrixAction (q.Extension 3) (matrixLongSection (q.Extension 3) s neg t) := by
  change imageRepresentation data (q.Extension 3)
    (fixedToModel (CartanMatrix.D 4) (q.Extension 3) CFSG.Models.triality
      (fun _ => q.order) (sourceLongSection q s neg t ht)) = _
  simp only [sourceLongSection,map_mul,map_inv,sourceLongTransport_toModel,
    longRoot_toModel,word_action,source_root_action,matrixLongSection]

theorem shortPositiveSection_action_mem_range (q : CFSG.PrimePower)
    (s : Fin 3) (t : Multiplicative (q.Extension 3)) :
    positiveAction (q.Extension 3)
      (shortPositiveSection (q.Extension 3) (definingFieldAutomorphism q 3) s t) ∈
        (fixedImageAction q).range := by
  refine ⟨sourceShortSection q s false t.toAdd,?_⟩
  rw [sourceShortSection_action]
  apply congrArg (matrixAction (q.Extension 3))
  apply Subtype.ext
  rw [matrixShortSection_val,positiveInclusion_val,shortPositiveSection_val]

theorem longPositiveSection_action_mem_range (q : CFSG.PrimePower)
    (s : Fin 3) (t : Multiplicative (q.Extension 3))
    (ht : definingFieldAutomorphism q 3 t.toAdd = t.toAdd) :
    positiveAction (q.Extension 3) (longPositiveSection (q.Extension 3) s t) ∈
      (fixedImageAction q).range := by
  refine ⟨sourceLongSection q s false t.toAdd ht,?_⟩
  rw [sourceLongSection_action]
  apply congrArg (matrixAction (q.Extension 3))
  apply Subtype.ext
  rw [matrixLongSection_val,positiveInclusion_val,longPositiveSection_val]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFixedSections
