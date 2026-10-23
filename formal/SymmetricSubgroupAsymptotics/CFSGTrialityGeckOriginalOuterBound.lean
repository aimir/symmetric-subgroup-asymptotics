import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalCommonField
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalParameterFaithfulness
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityNormalizedLabels
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsBounds
import Mathlib.Tactic.Group

/-! Actual original triality outer automorphisms have order at most the
literal cubic-field automorphism group. Both alignment steps are inner;
normalized signed parameters are determined by one field map. No
exceptional automorphism classification or supplied field-action
subgroup is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOuterBound
open CFSGTrialityGeckOriginalCommonField CFSGTrialityGeckOriginalParameterFaithfulness
open CFSGTrialityGeckOriginalPairAlignment CFSGTrialityGeckPositiveScalarNormalization
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityFixedField
open CFSGOuterCardinalityNormalizedLabels PrimitiveSocleRawStructure
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

private theorem postInner_eq_conj {G:Type*} [Group G] (d:G) (f:MulAut G) :
    postInner d f=MulAut.conj d*f := rfl

private theorem postInner_inner {G:Type*} [Group G] (d a:G) (f:MulAut G) :
    postInner d (postInner a f)=postInner (d*a) f := by
  apply MulEquiv.ext
  intro x
  change d*(a*f x*a⁻¹)*d⁻¹=(d*a)*f x*(d*a)⁻¹
  group

theorem original_inner_signed_field_description (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q)) :
    ∃g:CFSG.Models.TrialityD4 q,
      ∃sigma:q.Extension 3≃+*q.Extension 3,∃tau:fixedField q≃+*fixedField q,
      (∀t:fixedField q,(tau t:q.Extension 3)=sigma (t:q.Extension 3))∧
      (∀(neg:Bool) t,(postInner g f) (originalShortHom q neg (Multiplicative.ofAdd t))=
        originalShortHom q neg (Multiplicative.ofAdd (sigma t)))∧
      (∀(neg:Bool) (t:fixedField q),(postInner g f) (originalMiddleHom q neg (Multiplicative.ofAdd t))=
        originalMiddleHom q neg (Multiplicative.ofAdd (tau t))) := by
  obtain ⟨a,hp,hn⟩ := original_exists_inner_fix_pair q f
  rw [←postInner_eq_conj a f] at hp hn
  obtain ⟨d,_,sigma,tau,hres,hX,hY⟩ := exists_inner_signed_field_description q (postInner a f) hp hn
  have he := postInner_inner d a f
  rw [he] at hX hY
  exact ⟨d*a,sigma,tau,hres,hX,hY⟩

theorem original_outer_card_le_fieldAut (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Nat.card (Outer (CFSG.Models.TrialityD4 q))≤Nat.card (q.Extension 3≃+*q.Extension 3) := by
  classical
  letI : Finite (q.Extension 3≃+*q.Extension 3) := Finite.of_injective
    (fun sigma:q.Extension 3≃+*q.Extension 3=>(sigma:q.Extension 3→q.Extension 3)) DFunLike.coe_injective
  choose g sigma tau hres hX hY using original_inner_signed_field_description q
  let normal (f:MulAut (CFSG.Models.TrialityD4 q)) := postInner (g f) f
  apply outer_card_le_of_normalized_labels normal sigma
  · intro f
    exact ⟨g f,postInner_eq_conj (g f) f⟩
  · intro f h he
    apply normalized_aut_eq_of_same_field q (normal f) (normal h) (sigma f) (tau f) (tau h)
      (hres f) _ (hX f) _ (hY f) (hY h)
    · rw [he]
      exact hres h
    · rw [he]
      exact hX h

theorem original_outer_card_le_three_exponent (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Nat.card (Outer (CFSG.Models.TrialityD4 q))≤3*q.exponent := by
  have hc : Nat.card (q.Extension 3≃+*q.Extension 3)=3*q.exponent :=
    CFSGFiniteFieldAutomorphisms.card_galoisField_ringAut q.prime (3*q.exponent)
      (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt q.exponent_pos))
  exact (original_outer_card_le_fieldAut q).trans_eq hc

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOuterBound
