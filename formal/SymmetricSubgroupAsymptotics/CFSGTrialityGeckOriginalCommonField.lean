import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalShortTorus
import SymmetricSubgroupAsymptotics.CFSGTrialityNormFieldRestriction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveScalarNormalization

/-! The actual short-torus/middle-root relation forces the two signed
parameter field maps to be one literal cubic-field automorphism and its
restriction. Combined with inner scalar normalization this describes
all four signed charts of every original pair-fixing automorphism. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalCommonField
open CFSGTrialityGeckOriginalShortTorus CFSGTrialityGeckOriginalSignedSemilinear
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityGeckPositiveScalarNormalization
open CFSGTrialityGeckOriginalRootFamily CFSGTrialityGeckOriginalOppositeAlignment
open CFSGTrialityGeckOriginalPairNormalizer CFSGTrialityNormFieldRestriction
open CFSGTrialityNormTorusScalars CFSGTrialityFixedField

theorem original_norm_inverse_intertwiner (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (sigma : q.Extension 3≃+*q.Extension 3) (tau : fixedField q≃+*fixedField q)
    (hX : ∀(neg:Bool) t,f (originalShortHom q neg (Multiplicative.ofAdd t))=
      originalShortHom q neg (Multiplicative.ofAdd (sigma t)))
    (hY : ∀(neg:Bool) (t:fixedField q),f (originalMiddleHom q neg (Multiplicative.ofAdd t))=
      originalMiddleHom q neg (Multiplicative.ofAdd (tau t))) :
    ∀c:(q.Extension 3)ˣ,tau ((normUnits q c : fixedField q)⁻¹)=
      ((normUnits q (Units.map sigma.toMonoidHom c) : (fixedField q)ˣ) : fixedField q)⁻¹ := by
  intro c
  have hh := congrArg f (shortTorusElement_middle q c (1:fixedField q))
  simp only [map_mul,map_inv,shortTorusElement_covariance q f sigma hX,hY,map_one,mul_one] at hh
  rw [shortTorusElement_middle] at hh
  simp only [mul_one] at hh
  have he := congrArg Multiplicative.toAdd (originalMiddleHom_injective q false hh)
  exact he.symm

theorem original_common_field_restriction (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (sigma : q.Extension 3≃+*q.Extension 3) (tau : fixedField q≃+*fixedField q)
    (hX : ∀(neg:Bool) t,f (originalShortHom q neg (Multiplicative.ofAdd t))=
      originalShortHom q neg (Multiplicative.ofAdd (sigma t)))
    (hY : ∀(neg:Bool) (t:fixedField q),f (originalMiddleHom q neg (Multiplicative.ofAdd t))=
      originalMiddleHom q neg (Multiplicative.ofAdd (tau t))) :
    ∀t:fixedField q,(tau t:q.Extension 3)=sigma (t:q.Extension 3) :=
  restriction_eq_of_norm_inverse_relation q sigma tau (original_norm_inverse_intertwiner q f sigma tau hX hY)

theorem exists_inner_signed_field_description (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃d∈originalPairNormalizer q,
      ∃sigma:q.Extension 3≃+*q.Extension 3,∃tau:fixedField q≃+*fixedField q,
      (∀t:fixedField q,(tau t:q.Extension 3)=sigma (t:q.Extension 3))∧
      (∀(neg:Bool) t,(postInner d f) (originalShortHom q neg (Multiplicative.ofAdd t))=
        originalShortHom q neg (Multiplicative.ofAdd (sigma t)))∧
      (∀(neg:Bool) (t:fixedField q),(postInner d f) (originalMiddleHom q neg (Multiplicative.ofAdd t))=
        originalMiddleHom q neg (Multiplicative.ofAdd (tau t))) := by
  obtain ⟨d,hd,sigma,tau,hp',hn',hX,hY⟩ := exists_positive_normalized_pair_fixer q f hp hn
  have hsignedX := signed_short_parameter_action q (postInner d f) hp' hn' sigma hX
  have hsignedY := signed_middle_parameter_action q (postInner d f) hp' hn' tau hY
  exact ⟨d,hd,sigma,tau,original_common_field_restriction q (postInner d f) sigma tau hsignedX hsignedY,
    hsignedX,hsignedY⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalCommonField
