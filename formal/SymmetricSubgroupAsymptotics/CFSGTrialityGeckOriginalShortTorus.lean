import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSignedSemilinear
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMixedTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGTrialityNormTorusScalars
import Mathlib.Tactic.Ring

/-! Literal short torus words in the SAME original model, their action
on the middle parameter, and covariance under a proved signed short
field action. These group identities supply the actual cubic norm
intertwiner needed for the common-field restriction. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalShortTorus
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckOriginalSignedSemilinear CFSGTrialityGeckSignedSimpleParameters
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckShortParameterWeyl CFSGTrialityGeckShortTorusConjugation
open CFSGTrialityGeckMixedTorusConjugation CFSGTrialityNormTorusScalars
open CFSGTrialityFixedField CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

def shortTorusGenerated (q : CFSG.PrimePower) (c : (q.Extension 3)ˣ) :
    fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
  (shortGeneratedHom q false (Multiplicative.ofAdd (c:q.Extension 3))*
    shortGeneratedHom q true (Multiplicative.ofAdd (-(c:q.Extension 3)⁻¹))*
    shortGeneratedHom q false (Multiplicative.ofAdd (c:q.Extension 3)))*
  (shortGeneratedHom q false (Multiplicative.ofAdd 1)*
    shortGeneratedHom q true (Multiplicative.ofAdd (-1))*shortGeneratedHom q false (Multiplicative.ofAdd 1))⁻¹

theorem shortTorusGenerated_val (q : CFSG.PrimePower) (c : (q.Extension 3)ˣ) :
    (shortTorusGenerated q c).val=shortTorusWord (q.Extension 3) (definingFieldAutomorphism q 3) c := by
  change (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false (c:q.Extension 3)*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-(c:q.Extension 3)⁻¹)*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false (c:q.Extension 3))*
    (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) true (-1)*
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false 1)⁻¹=_
  simp only [shortTorusWord,shortWeylWord,Units.val_one,inv_one]

def shortTorusElement (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (c : (q.Extension 3)ˣ) : CFSG.Models.TrialityD4 q := generatedToOriginal q (shortTorusGenerated q c)

theorem shortTorusElement_word (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (c : (q.Extension 3)ˣ) :
    shortTorusElement q c=
      (originalShortHom q false (Multiplicative.ofAdd (c:q.Extension 3))*
        originalShortHom q true (Multiplicative.ofAdd (-(c:q.Extension 3)⁻¹))*
        originalShortHom q false (Multiplicative.ofAdd (c:q.Extension 3)))*
      (originalShortHom q false (Multiplicative.ofAdd 1)*
        originalShortHom q true (Multiplicative.ofAdd (-1))*originalShortHom q false (Multiplicative.ofAdd 1))⁻¹ := by
  simp only [shortTorusElement,shortTorusGenerated,originalShortHom,MonoidHom.comp_apply,map_mul,map_inv]

theorem shortTorusElement_covariance (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (sigma : q.Extension 3≃+*q.Extension 3)
    (hX : ∀(neg:Bool) t,f (originalShortHom q neg (Multiplicative.ofAdd t))=
      originalShortHom q neg (Multiplicative.ofAdd (sigma t))) (c : (q.Extension 3)ˣ) :
    f (shortTorusElement q c)=shortTorusElement q (Units.map sigma.toMonoidHom c) := by
  simp only [shortTorusElement_word,map_mul,map_inv,hX,map_one,map_neg,map_inv₀,Units.coe_map]
  rfl

theorem shortTorusElement_middle (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (c : (q.Extension 3)ˣ) (t : fixedField q) :
    shortTorusElement q c*originalMiddleHom q false (Multiplicative.ofAdd t)*(shortTorusElement q c)⁻¹=
      originalMiddleHom q false (Multiplicative.ofAdd ((normUnits q c : fixedField q)⁻¹*t)) := by
  have hraw : shortTorusGenerated q c*middleGeneratedHom q false (Multiplicative.ofAdd t)*
      (shortTorusGenerated q c)⁻¹=middleGeneratedHom q false
        (Multiplicative.ofAdd ((normUnits q c : fixedField q)⁻¹*t)) := by
    apply Subtype.ext
    change (shortTorusGenerated q c).val*canonicalRoot rawData (q.Extension 3) false 1 t.val*
      (shortTorusGenerated q c).val⁻¹=
      canonicalRoot rawData (q.Extension 3) false 1 ((normUnits q c : fixedField q)⁻¹*t).val
    simp only [shortTorusGenerated_val]
    rw [shortTorus_middle]
    congr 1
    simp only [normUnits,Units.coe_map,Subfield.coe_mul,Subfield.coe_inv]
    change t.val*((c:q.Extension 3)*definingFieldAutomorphism q 3 (c:q.Extension 3)*
      definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 (c:q.Extension 3)))⁻¹=
      ((c:q.Extension 3)*definingFieldAutomorphism q 3 (c:q.Extension 3)*
        definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 (c:q.Extension 3)))⁻¹*t.val
    ring
  simpa only [map_mul,map_inv,shortTorusElement,originalMiddleHom,MonoidHom.comp_apply] using
    congrArg (generatedToOriginal q) hraw

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalShortTorus
