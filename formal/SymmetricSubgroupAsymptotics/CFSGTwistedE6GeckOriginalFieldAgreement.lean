import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMiddleFieldAction

/-! The two actual A2 fields agree on the fixed subfield. The proved
middle commutator is compared in the ORIGINAL group, and its paired
parameter is recovered using the genuinely injective positive restriction.
The coefficient-one ab term works also in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalFieldAgreement
open CFSGTwistedE6GeckOriginalMiddleFieldAction CFSGTwistedE6GeckOriginalMiddleCollecting
open CFSGTwistedE6GeckMiddleGeneratedFactors CFSGTwistedE6GeckRelativeTorus
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalPairedSignedField CFSGTwistedE6GeckOriginalSingletonSignedField

theorem fields_agree_on_fixed (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (f : MulAut (CFSG.Models.TwistedE6 q)) (tau : RingAut (q.Extension 2)) (kap : RingAut (Coefficient q))
    (d : (q.Extension 2)ˣ) (e : (Coefficient q)ˣ)
    (hpair : ∀a,f (pairedOriginalHom q false 1 (Multiplicative.ofAdd a))=
      pairedOriginalHom q false 1 (Multiplicative.ofAdd ((d : q.Extension 2)*tau a)))
    (hpairneg : ∀a,f (pairedOriginalHom q true 1 (Multiplicative.ofAdd a))=
      pairedOriginalHom q true 1 (Multiplicative.ofAdd ((d : q.Extension 2)⁻¹*tau a)))
    (hsingle : ∀a,f (singletonOriginalHom q false 1 (Multiplicative.ofAdd a))=
      singletonOriginalHom q false 1 (Multiplicative.ofAdd ((e : Coefficient q)*kap a)))
    (hsingleneg : ∀a,f (singletonOriginalHom q true 1 (Multiplicative.ofAdd a))=
      singletonOriginalHom q true 1 (Multiplicative.ofAdd ((e : Coefficient q)⁻¹*kap a)))
    (b : Coefficient q) : tau (b : q.Extension 2)=(kap b : q.Extension 2) := by
  have hR := middleLong_image q f tau kap d e hpair hpairneg hsingle
  have hS := middleShort_image q f tau kap d e hpair hsingle hsingleneg
  have he := congrArg f (original_middle_commutator q (1 : q.Extension 2) b)
  rw [map_commutatorElement,hpair,hsingle,map_one tau,mul_one] at he
  rw [map_mul f] at he
  rw [hR,hS] at he
  rw [original_middle_commutator] at he
  have hp := original_middleFactor_snd_eq q _ _ _ _ he
  simp only [one_mul,map_neg,mul_neg] at hp
  have hc : (d : q.Extension 2)*(((e : Coefficient q)*kap b : Coefficient q) : q.Extension 2)=
      (((e : Coefficient q) : q.Extension 2)*(d : q.Extension 2))*tau (b : q.Extension 2) := neg_inj.mp hp
  apply mul_left_cancel₀ (mul_ne_zero (coefficientUnit q e).ne_zero d.ne_zero)
  calc
    _=(d : q.Extension 2)*(((e : Coefficient q)*kap b : Coefficient q) : q.Extension 2) := hc.symm
    _=_ := by
      change (d : q.Extension 2)*(((e : Coefficient q) : q.Extension 2)*(kap b : q.Extension 2))=
        (((e : Coefficient q) : q.Extension 2)*(d : q.Extension 2))*(kap b : q.Extension 2)
      ring

theorem exists_compatible_positive_fields (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃ (tau : RingAut (q.Extension 2)) (kap : RingAut (Coefficient q))
      (c d : q.Extension 2) (e h : Coefficient q),
      c≠0 ∧ d≠0 ∧ e≠0 ∧ h≠0 ∧
      (∀b : Coefficient q,tau (b : q.Extension 2)=(kap b : q.Extension 2)) ∧
      (∀a : q.Extension 2,
        f (pairedOriginalHom q false 0 (Multiplicative.ofAdd a))=pairedOriginalHom q false 0 (Multiplicative.ofAdd (c*tau a)) ∧
        f (pairedOriginalHom q false 1 (Multiplicative.ofAdd a))=pairedOriginalHom q false 1 (Multiplicative.ofAdd (d*tau a))) ∧
      (∀b : Coefficient q,
        f (singletonOriginalHom q false 0 (Multiplicative.ofAdd b))=singletonOriginalHom q false 0 (Multiplicative.ofAdd (e*kap b)) ∧
        f (singletonOriginalHom q false 1 (Multiplicative.ofAdd b))=singletonOriginalHom q false 1 (Multiplicative.ofAdd (h*kap b))) := by
  obtain ⟨tau,c,d,hc,hd,hp⟩ := paired_signed_parameters_common_field q f hU hV
  obtain ⟨kap,e,h,he,hh,hs⟩ := singleton_signed_parameters_common_field q f hU hV
  refine ⟨tau,kap,c,d,e,h,hc,hd,he,hh,?_,?_,?_⟩
  · exact fields_agree_on_fixed q f tau kap (Units.mk0 d hd) (Units.mk0 h hh)
      (fun a=>(hp a).2.1) (fun a=>(hp a).2.2.2)
      (fun b=>(hs b).2.1) (fun b=>(hs b).2.2.2)
  · intro a
    exact ⟨(hp a).1,(hp a).2.1⟩
  · intro b
    exact ⟨(hs b).1,(hs b).2.1⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalFieldAgreement
