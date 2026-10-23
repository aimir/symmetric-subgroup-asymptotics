import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongA2Commutator
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFixedSections

/-! Every positive long section acts as a member of the DERIVED original
triality fixed subgroup.  A literal A2 commutator gives the highest long
root; actual fixed Weyl transports give the other two.  No small-field
exception, division by two or three, or source-faithfulness premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckLongA2Commutator CFSGTrialityGeckOriginalFixedSections
open CFSGTrialityGeckSourceWordAction CFSGTrialityTripleFixedRoots
open CFSGTrialityFixedWeylWords CFSGSerreFixedRootElements CFSGSerreOrdinaryTwists
open CFSGTrialityGeckSectionQuotientCoordinates CFSGTrialityGeckDiagramCovariance

def derivedImageAction (q : CFSG.PrimePower) :
    commutator (Fixed q) →* (Image (q.Extension 3) ≃ₗ[q.Extension 3] Image (q.Extension 3)) :=
  (fixedImageAction q).comp (commutator (Fixed q)).subtype

theorem commutator_image_mem (q : CFSG.PrimePower) (g h : Fixed q) :
    ⁅fixedImageAction q g,fixedImageAction q h⁆ ∈ (derivedImageAction q).range := by
  refine ⟨derivedCommutator (CartanMatrix.D 4) (q.Extension 3)
    CFSG.Models.triality (fun _ => q.order) g h,?_⟩
  change fixedImageAction q ⁅g,h⁆ = _
  exact map_commutatorElement (fixedImageAction q) g h

theorem conjugate_image_mem (q : CFSG.PrimePower) (g d : Fixed q)
    (hd : fixedImageAction q d ∈ (derivedImageAction q).range) :
    fixedImageAction q (g*d*g⁻¹) ∈ (derivedImageAction q).range := by
  obtain ⟨z,hz⟩ := hd
  refine ⟨⟨g*z.val*g⁻¹,
    (inferInstance : (commutator (Fixed q)).Normal).conj_mem z.val z.property g⟩,?_⟩
  change fixedImageAction q (g*z.val*g⁻¹) = fixedImageAction q (g*d*g⁻¹)
  have he : fixedImageAction q z.val = fixedImageAction q d := hz
  rw [map_mul,map_mul,map_mul,map_mul,he]

theorem highest_long_action_mem_derived (q : CFSG.PrimePower) (t : q.Extension 3)
    (ht : t^q.order = t) :
    fixedImageAction q (sourceLongSection q 2 false t ht) ∈ (derivedImageAction q).range := by
  obtain ⟨ε,hε,hcomm⟩ := long_commutator_sign
  let a : q.Extension 3 := (ε : q.Extension 3)*t
  have ha : a^q.order = a := by
    change definingFieldAutomorphism q 3 a = a
    change definingFieldAutomorphism q 3 ((ε : q.Extension 3)*t) = (ε : q.Extension 3)*t
    rw [map_mul,map_intCast,definingFieldAutomorphism_apply,ht]
  let g0 := sourceLongSection q 0 false a ha
  let g1 := sourceLongSection q 1 false 1 (one_pow q.order)
  have hm := commutator_image_mem q g0 g1
  have hcoeff : (ε : q.Extension 3)*(a*1) = t := by
    dsimp only [a]
    rcases hε with rfl|rfl <;> simp
  have hword : ⁅matrixLongSection (q.Extension 3) 0 false a,
      matrixLongSection (q.Extension 3) 1 false 1⁆ =
        matrixLongSection (q.Extension 3) 2 false t := by
    apply Subtype.ext
    simp only [commutatorElement_def,Subgroup.coe_mul,Subgroup.coe_inv,matrixLongSection_val]
    exact (hcomm (q.Extension 3) a 1).trans
      (congrArg (CFSGTrialityGeckFixedRootSections.longSection (q.Extension 3) 2 false) hcoeff)
  have he : ⁅fixedImageAction q g0,fixedImageAction q g1⁆ =
      fixedImageAction q (sourceLongSection q 2 false t ht) := by
    dsimp only [g0,g1]
    rw [sourceLongSection_action,sourceLongSection_action,sourceLongSection_action,
      ← map_commutatorElement,hword]
  exact he ▸ hm

theorem long_source_action_mem_derived (q : CFSG.PrimePower) (s : Fin 3)
    (t : q.Extension 3) (ht : t^q.order = t) :
    fixedImageAction q (sourceLongSection q s false t ht) ∈ (derivedImageAction q).range := by
  have h2 := highest_long_action_mem_derived q t ht
  have h1 : fixedImageAction q (sourceLongSection q 1 false t ht) ∈
      (derivedImageAction q).range := by
    have hm := conjugate_image_mem q (longWeyl q)⁻¹ (sourceLongSection q 2 false t ht) h2
    have he : (longWeyl q)⁻¹ * sourceLongSection q 2 false t ht * ((longWeyl q)⁻¹)⁻¹ =
        sourceLongSection q 1 false t ht := by
      dsimp only [sourceLongSection,sourceLongTransport]
      change (longWeyl q)⁻¹ *
        ((longWeyl q*shortWeyl q)*longRoot q false t ht*(longWeyl q*shortWeyl q)⁻¹) *
        ((longWeyl q)⁻¹)⁻¹ = shortWeyl q*longRoot q false t ht*(shortWeyl q)⁻¹
      group
    rw [he] at hm
    exact hm
  have h0 : fixedImageAction q (sourceLongSection q 0 false t ht) ∈
      (derivedImageAction q).range := by
    have hm := conjugate_image_mem q (shortWeyl q)⁻¹ (sourceLongSection q 1 false t ht) h1
    have he : (shortWeyl q)⁻¹ * sourceLongSection q 1 false t ht * ((shortWeyl q)⁻¹)⁻¹ =
        sourceLongSection q 0 false t ht := by
      dsimp only [sourceLongSection,sourceLongTransport]
      change (shortWeyl q)⁻¹ * (shortWeyl q*longRoot q false t ht*(shortWeyl q)⁻¹) *
        ((shortWeyl q)⁻¹)⁻¹ = (1 : Fixed q)*longRoot q false t ht*(1 : Fixed q)⁻¹
      group
    rw [he] at hm
    exact hm
  fin_cases s
  · exact h0
  · exact h1
  · exact h2

theorem long_positive_action_mem_derived (q : CFSG.PrimePower)
    (s : Fin 3) (t : Multiplicative (q.Extension 3))
    (ht : definingFieldAutomorphism q 3 t.toAdd = t.toAdd) :
    positiveAction (q.Extension 3) (longPositiveSection (q.Extension 3) s t) ∈
      (derivedImageAction q).range := by
  have hm := long_source_action_mem_derived q s t.toAdd ht
  have he : fixedImageAction q (sourceLongSection q s false t.toAdd ht) =
      positiveAction (q.Extension 3) (longPositiveSection (q.Extension 3) s t) := by
    rw [sourceLongSection_action]
    apply congrArg (matrixAction (q.Extension 3))
    apply Subtype.ext
    rw [matrixLongSection_val,positiveInclusion_val,longPositiveSection_val]
  exact he ▸ hm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongDerivedImage
