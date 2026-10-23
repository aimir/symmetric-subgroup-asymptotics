import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalParameterFaithful

/-! Six ambient positive scalar actions determine an element of the
ORIGINAL opposed-pair normalizer modulo its trivial original centre.
The scalars need not satisfy any asserted fixed-field relations. This
coarse count is sufficient for the large-degree class bound. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairNormalizerCardinality
open CFSGTwistedE6GeckOriginalPairNormalizer CFSGTwistedE6GeckOriginalParameterFaithful
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalSimpleParameters CFSGTwistedE6GeckOriginalSingletonA2
open CFSGTwistedE6GeckRelativeTorus CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2 CFSGSerreOrdinaryTwists
open CFSGSerreQuadraticMatrix

private theorem map_conj_eq {G:Type*} [Group G] (P:Subgroup G) (d:G)
    (hd:d∈Subgroup.normalizer (P:Set G)) : P.map (MulAut.conj d).toMonoidHom=P := by
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hd

private theorem positive_fixed_of_raw_fixed (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (z:fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))
    (hz:∀i t,z.val*canonicalRoot rawData (q.Extension 2) false i t*z.val⁻¹=
      canonicalRoot rawData (q.Extension 2) false i t) :
    (∀j a,generatedToOriginal q z*pairedOriginalHom q false j (Multiplicative.ofAdd a)*
      (generatedToOriginal q z)⁻¹=pairedOriginalHom q false j (Multiplicative.ofAdd a))∧
    (∀j (a:Coefficient q),generatedToOriginal q z*singletonOriginalHom q false j (Multiplicative.ofAdd a)*
      (generatedToOriginal q z)⁻¹=singletonOriginalHom q false j (Multiplicative.ofAdd a)) := by
  constructor
  · intro j a
    have hJ : z*pairedSignedInGenerated q false j (Multiplicative.ofAdd a)*z⁻¹=
        pairedSignedInGenerated q false j (Multiplicative.ofAdd a) := by
      apply Subtype.ext
      change z.val*(canonicalRoot rawData (q.Extension 2) false (pairedNode j) a*
        canonicalRoot rawData (q.Extension 2) false (pairedPartner j) (definingFieldAutomorphism q 2 a))*
          z.val⁻¹=_
      calc
        _=(z.val*canonicalRoot rawData (q.Extension 2) false (pairedNode j) a*z.val⁻¹)*
          (z.val*canonicalRoot rawData (q.Extension 2) false (pairedPartner j)
            (definingFieldAutomorphism q 2 a)*z.val⁻¹) := by group
        _=_ := by rw [hz,hz];rfl
    have hp := congrArg (generatedToOriginal q) hJ
    rw [map_mul,map_mul,map_inv] at hp
    exact hp
  · intro j a
    have hJ : z*singletonSignedInGenerated q false j (Multiplicative.ofAdd a)*z⁻¹=
        singletonSignedInGenerated q false j (Multiplicative.ofAdd a) := by
      apply Subtype.ext
      exact hz (node j) (a:q.Extension 2)
    have hp := congrArg (generatedToOriginal q) hJ
    rw [map_mul,map_mul,map_inv] at hp
    exact hp

private theorem center_eq_bot (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (hn:¬IsMulCommutative (CFSG.Models.TwistedE6 q)) :
    Subgroup.center (CFSG.Models.TwistedE6 q)=⊥ := by
  rcases (inferInstance : (Subgroup.center (CFSG.Models.TwistedE6 q)).Normal).eq_bot_or_eq_top with hc|hc
  · exact hc
  · exact (hn (Subgroup.center_eq_top_iff.mp hc)).elim

theorem originalPairNormalizer_card_le (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (hn:¬IsMulCommutative (CFSG.Models.TwistedE6 q)) :
    Nat.card (originalPairNormalizer q)≤q.order^12 := by
  letI : Finite (CFSG.Models.TwistedE6 q) := original_finite q
  choose g hg c hc using fun d:originalPairNormalizer q=>
    originalPairNormalizer_raw_positive_scalars q d.val d.property
  let encode : originalPairNormalizer q→Fin 6→(q.Extension 2)ˣ := c
  have hinj : Function.Injective encode := by
    intro d e he
    let z := (g e)⁻¹*g d
    let Z : originalPairNormalizer q := e⁻¹*d
    have hzO : generatedToOriginal q z=Z.val := by
      change generatedToOriginal q ((g e)⁻¹*g d)=e.val⁻¹*d.val
      rw [map_mul,map_inv,hg e,hg d]
    have hz (i:Fin 6) (t:q.Extension 2) :
        z.val*canonicalRoot rawData (q.Extension 2) false i t*z.val⁻¹=
          canonicalRoot rawData (q.Extension 2) false i t := by
      have hact : (g d).val*canonicalRoot rawData (q.Extension 2) false i t*(g d).val⁻¹=
          (g e).val*canonicalRoot rawData (q.Extension 2) false i t*(g e).val⁻¹ := by
        rw [hc d,hc e,show c d i=c e i from congrFun he i]
      change ((g e).val⁻¹*(g d).val)*canonicalRoot rawData (q.Extension 2) false i t*
        ((g e).val⁻¹*(g d).val)⁻¹=_
      calc
        _=(g e).val⁻¹*((g d).val*canonicalRoot rawData (q.Extension 2) false i t*(g d).val⁻¹)*(g e).val := by group
        _=(g e).val⁻¹*((g e).val*canonicalRoot rawData (q.Extension 2) false i t*(g e).val⁻¹)*(g e).val :=
          congrArg (fun x=>(g e).val⁻¹*x*(g e).val) hact
        _=_ := by group
    obtain ⟨hp,hs⟩ := positive_fixed_of_raw_fixed q z hz
    rw [hzO] at hp hs
    let f := MulAut.conj Z.val
    have hf : f=1 := eq_one_of_positive_simple_parameters_fixed q f
      (map_conj_eq _ Z.val Z.property.1) (map_conj_eq _ Z.val Z.property.2) hp hs
    have hcenter : Z.val∈Subgroup.center (CFSG.Models.TwistedE6 q) := by
      apply Subgroup.mem_center_iff.mpr
      intro x
      have hh : Z.val*x*Z.val⁻¹=x := congrArg (fun A:MulAut (CFSG.Models.TwistedE6 q)=>A x) hf
      have hc := congrArg (fun a=>a*Z.val) hh
      have hcomm : Z.val*x=x*Z.val := by simpa only [mul_assoc,inv_mul_cancel,mul_one] using hc
      exact hcomm.symm
    rw [center_eq_bot q hn] at hcenter
    have hz1 : e.val⁻¹*d.val=1 := Subgroup.mem_bot.mp hcenter
    exact Subtype.ext (inv_mul_eq_one.mp hz1).symm
  have hu : Nat.card (q.Extension 2)ˣ≤Nat.card (q.Extension 2) :=
    Nat.card_le_card_of_injective (fun x:(q.Extension 2)ˣ=>(x:q.Extension 2)) Units.val_injective
  calc
    Nat.card (originalPairNormalizer q)≤Nat.card (Fin 6→(q.Extension 2)ˣ) :=
      Nat.card_le_card_of_injective encode hinj
    _=Nat.card ((q.Extension 2)ˣ)^6 := by rw [Nat.card_fun,Nat.card_fin]
    _≤Nat.card (q.Extension 2)^6 := Nat.pow_le_pow_left hu 6
    _=q.order^12 := by rw [CFSGTwistedANaturalMatrices.extension_two_card,←pow_mul]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairNormalizerCardinality
