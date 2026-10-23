import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPairNormalizerScalars
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeScalarTorusNormalizer

/-! Both scalar bounds and every scalar-realizing word are transported
to the intrinsic pair normalizer in the SAME original model. Only the
actual central quotient, its surjectivity, and proved literal parameter
identities are used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairScalarAction
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckOriginalPairNormalizer CFSGTrialityGeckPairNormalizerScalars
open CFSGTrialityGeckRelativeScalarTorusNormalizer CFSGTrialityGeckOriginalSimpleParameters
open CFSGTrialityGeckSignedSimpleParameters CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckFixedRootWords
open CFSGTrialityFixedField CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem map_short_action (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (g : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) (c : (q.Extension 3)ˣ)
    (hc : ∀t,g.val*shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t*g.val⁻¹=
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false ((c:q.Extension 3)*t)) :
    ∀t,generatedToOriginal q g*originalShortHom q false (Multiplicative.ofAdd t)*
      (generatedToOriginal q g)⁻¹=originalShortHom q false (Multiplicative.ofAdd ((c:q.Extension 3)*t)) := by
  intro t
  have hh : g*shortGeneratedHom q false (Multiplicative.ofAdd t)*g⁻¹=
      shortGeneratedHom q false (Multiplicative.ofAdd ((c:q.Extension 3)*t)) := Subtype.ext (hc t)
  simpa only [map_mul,map_inv,originalShortHom,MonoidHom.comp_apply] using
    congrArg (generatedToOriginal q) hh

private theorem map_middle_action (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (g : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) (a : (fixedField q)ˣ)
    (ha : ∀t:fixedField q,g.val*canonicalRoot rawData (q.Extension 3) false 1 t.val*g.val⁻¹=
      canonicalRoot rawData (q.Extension 3) false 1 ((a:fixedField q)*t).val) :
    ∀t:fixedField q,generatedToOriginal q g*originalMiddleHom q false (Multiplicative.ofAdd t)*
      (generatedToOriginal q g)⁻¹=originalMiddleHom q false (Multiplicative.ofAdd ((a:fixedField q)*t)) := by
  intro t
  have hh : g*middleGeneratedHom q false (Multiplicative.ofAdd t)*g⁻¹=
      middleGeneratedHom q false (Multiplicative.ofAdd ((a:fixedField q)*t)) := Subtype.ext (ha t)
  simpa only [map_mul,map_inv,originalMiddleHom,MonoidHom.comp_apply] using
    congrArg (generatedToOriginal q) hh

theorem originalPairNormalizer_positive_scalars (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (d : CFSG.Models.TrialityD4 q) (hd : d∈originalPairNormalizer q) :
    ∃c:(q.Extension 3)ˣ,∃a:(fixedField q)ˣ,
      (∀t,d*originalShortHom q false (Multiplicative.ofAdd t)*d⁻¹=
        originalShortHom q false (Multiplicative.ofAdd ((c:q.Extension 3)*t)))∧
      (∀t:fixedField q,d*originalMiddleHom q false (Multiplicative.ofAdd t)*d⁻¹=
        originalMiddleHom q false (Multiplicative.ofAdd ((a:fixedField q)*t))) := by
  obtain ⟨g,rfl⟩ := generatedToOriginal_surjective q d
  obtain ⟨c,a,hc,ha⟩ := pairNormalizer_positive_scalars q g.val
    ((mem_originalPairNormalizer_iff q g).mp hd)
  exact ⟨c,a,map_short_action q g c hc,map_middle_action q g a ha⟩

theorem originalPairNormalizer_realizes_scalars (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (c : (q.Extension 3)ˣ) (a : (fixedField q)ˣ) :
    ∃d∈originalPairNormalizer q,
      (∀t,d*originalShortHom q false (Multiplicative.ofAdd t)*d⁻¹=
        originalShortHom q false (Multiplicative.ofAdd ((c:q.Extension 3)*t)))∧
      (∀t:fixedField q,d*originalMiddleHom q false (Multiplicative.ofAdd t)*d⁻¹=
        originalMiddleHom q false (Multiplicative.ofAdd ((a:fixedField q)*t))) := by
  obtain ⟨d,hd,hc,ha⟩ := exists_scalar_word_in_pairNormalizer q c a
  let g : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) := ⟨d,hd.2⟩
  refine ⟨generatedToOriginal q g,(mem_originalPairNormalizer_iff q g).mpr hd,
    map_short_action q g c hc,map_middle_action q g a ha⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairScalarAction
