import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairScalarAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSignedSemilinear
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalParameterFaithfulness

/-! The ORIGINAL opposed-pair normalizer has at most q^4 elements.
Its two actual scalar actions are faithful modulo the original centre;
no converse identification with the generated torus is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPairNormalizerCardinality
open CFSGTrialityGeckOriginalPairNormalizer CFSGTrialityGeckOriginalPairScalarAction
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityGeckOriginalSignedSemilinear
open CFSGTrialityGeckOriginalParameterFaithfulness CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckOriginalRootFamily CFSGTrialityGeckOriginalOppositeAlignment
open CFSGTrialityFixedField CFSGSerreOrdinaryTwists CFSGTrialityGeckRelativeRootGenerated

private theorem map_conj_eq {G:Type*} [Group G] (P:Subgroup G) (d:G)
    (hd:d∈Subgroup.normalizer (P:Set G)) :
    P.map (MulAut.conj d).toMonoidHom=P := by
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hd

private theorem eq_of_positive_scalars_eq (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (hn:¬IsMulCommutative (CFSG.Models.TrialityD4 q))
    (d e:originalPairNormalizer q)
    (hX:∀t,d.val*originalShortHom q false (Multiplicative.ofAdd t)*d.val⁻¹=
      e.val*originalShortHom q false (Multiplicative.ofAdd t)*e.val⁻¹)
    (hY:∀t:fixedField q,d.val*originalMiddleHom q false (Multiplicative.ofAdd t)*d.val⁻¹=
      e.val*originalMiddleHom q false (Multiplicative.ofAdd t)*e.val⁻¹) : d=e := by
  let z := e⁻¹*d
  let f := MulAut.conj z.val
  have hp : (originalSylow q).map f.toMonoidHom=originalSylow q :=
    map_conj_eq _ z.val z.property.1
  have hv : (originalNegative q).map f.toMonoidHom=originalNegative q :=
    map_conj_eq _ z.val z.property.2
  have hx (t:q.Extension 3) : f (originalShortHom q false (Multiplicative.ofAdd t))=
      originalShortHom q false (Multiplicative.ofAdd t) := by
    change (e.val⁻¹*d.val)*originalShortHom q false (Multiplicative.ofAdd t)*(e.val⁻¹*d.val)⁻¹=_
    calc
      _=e.val⁻¹*(d.val*originalShortHom q false (Multiplicative.ofAdd t)*d.val⁻¹)*e.val := by group
      _=e.val⁻¹*(e.val*originalShortHom q false (Multiplicative.ofAdd t)*e.val⁻¹)*e.val :=
        congrArg (fun a=>e.val⁻¹*a*e.val) (hX t)
      _=_ := by group
  have hy (t:fixedField q) : f (originalMiddleHom q false (Multiplicative.ofAdd t))=
      originalMiddleHom q false (Multiplicative.ofAdd t) := by
    change (e.val⁻¹*d.val)*originalMiddleHom q false (Multiplicative.ofAdd t)*(e.val⁻¹*d.val)⁻¹=_
    calc
      _=e.val⁻¹*(d.val*originalMiddleHom q false (Multiplicative.ofAdd t)*d.val⁻¹)*e.val := by group
      _=e.val⁻¹*(e.val*originalMiddleHom q false (Multiplicative.ofAdd t)*e.val⁻¹)*e.val :=
        congrArg (fun a=>e.val⁻¹*a*e.val) (hY t)
      _=_ := by group
  have hf : f=1 := original_aut_ext q f 1
    (signed_short_parameter_action q f hp hv (RingEquiv.refl _) hx)
    (signed_middle_parameter_action q f hp hv (RingEquiv.refl _) hy)
  have hcenter : Subgroup.center (CFSG.Models.TrialityD4 q)=⊥ := by
    rcases (inferInstance : (Subgroup.center (CFSG.Models.TrialityD4 q)).Normal).eq_bot_or_eq_top with hc|hc
    · exact hc
    · exact (hn (Subgroup.center_eq_top_iff.mp hc)).elim
  have hz : z.val∈Subgroup.center (CFSG.Models.TrialityD4 q) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    have he : z.val*x*z.val⁻¹=x := congrArg (fun A:MulAut (CFSG.Models.TrialityD4 q)=>A x) hf
    have hh := congrArg (fun a=>a*z.val) he
    have hc : z.val*x=x*z.val := by
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
    exact hc.symm
  rw [hcenter] at hz
  have hz1 : e.val⁻¹*d.val=1 := Subgroup.mem_bot.mp hz
  exact Subtype.ext (inv_mul_eq_one.mp hz1).symm

theorem originalPairNormalizer_card_le (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (hn:¬IsMulCommutative (CFSG.Models.TrialityD4 q)) :
    Nat.card (originalPairNormalizer q)≤q.order^4 := by
  letI : Finite (CFSG.Models.TrialityD4 q) := Finite.of_surjective
    (generatedToOriginal q) (generatedToOriginal_surjective q)
  choose c a hX hY using fun d:originalPairNormalizer q=>
    originalPairNormalizer_positive_scalars q d.val d.property
  let encode : originalPairNormalizer q→(q.Extension 3)ˣ×(fixedField q)ˣ := fun d=>(c d,a d)
  have hinj : Function.Injective encode := by
    intro d e he
    have hc : c d=c e := congrArg Prod.fst he
    have ha : a d=a e := congrArg Prod.snd he
    apply eq_of_positive_scalars_eq q hn d e
    · intro t
      exact (hX d t).trans (by rw [hc];exact (hX e t).symm)
    · intro t
      exact (hY d t).trans (by rw [ha];exact (hY e t).symm)
  have hcx : Nat.card ((q.Extension 3)ˣ)≤Nat.card (q.Extension 3) :=
    Nat.card_le_card_of_injective (fun x:(q.Extension 3)ˣ=>(x:q.Extension 3)) Units.val_injective
  have hca : Nat.card ((fixedField q)ˣ)≤Nat.card (fixedField q) :=
    Nat.card_le_card_of_injective (fun x:(fixedField q)ˣ=>(x:fixedField q)) Units.val_injective
  calc
    Nat.card (originalPairNormalizer q)≤Nat.card ((q.Extension 3)ˣ×(fixedField q)ˣ) :=
      Nat.card_le_card_of_injective encode hinj
    _=Nat.card ((q.Extension 3)ˣ)*Nat.card ((fixedField q)ˣ) := Nat.card_prod _ _
    _≤Nat.card (q.Extension 3)*Nat.card (fixedField q) := Nat.mul_le_mul hcx hca
    _=q.order^4 := by
      rw [CFSGTrialityTripleFixedRoots.extension_three_card,fixedField_card]
      ring

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPairNormalizerCardinality
