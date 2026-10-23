import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairScalarAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalParameterFaithful
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSignedPathAction

/-! The actual ORIGINAL F4 opposed-pair normalizer has at most |K|^4
elements. Four literal scalar actions are faithful modulo the original
centre, which is trivial in the noncommutative simple case. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PairNormalizerCardinality
open CFSGFFourE6OriginalPairScalarAction CFSGFFourE6OriginalParameterFaithful
open CFSGFFourE6OriginalSignedPathAction CFSGFFourE6OriginalSimpleParameters
open CFSGFFourE6GeneratedOriginalProjection CFSGFFourE6OriginalProjection
open CFSGFFourE6OriginalOppositeAlignment CFSGSignedSubgroupPermutationAgreement
open CFSG.Models.Chevalley

private theorem map_conj_eq {G:Type*} [Group G] (P:Subgroup G) (d:G)
    (hd:d∈Subgroup.normalizer (P:Set G)) : P.map (MulAut.conj d).toMonoidHom=P := by
  apply SetLike.coe_injective
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hd

private theorem range_map_eq_of_fixed {K G:Type*} [Field K] [Group G]
    (X:Multiplicative K→*G) (f:MulAut G)
    (h:∀a:K,f (X (Multiplicative.ofAdd a))=X (Multiplicative.ofAdd a)) :
    X.range.map f.toMonoidHom=X.range := by
  ext y
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    rw [show f.toMonoidHom (X a)=X a from h a.toAdd]
    exact ⟨a,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨X a,⟨a,rfl⟩,h a.toAdd⟩

private theorem eq_one_of_pair_and_positive_fixed (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f:MulAut (Projective CartanMatrix.F₄ K))
    (hU:(originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map f.toMonoidHom=
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)))
    (hV:(originalNegative K).map f.toMonoidHom=originalNegative K)
    (hpos:∀i a,f (originalSimpleHom K false i (Multiplicative.ofAdd a))=
      originalSimpleHom K false i (Multiplicative.ofAdd a)) : f=1 := by
  obtain ⟨sigma,hsigma⟩ := exists_original_signed_path_permutation K p f hU hV
  have hp (i:Fin 4) : (originalSimpleHom K false i).range.map f.toMonoidHom=
      (originalSimpleHom K false i).range := range_map_eq_of_fixed _ f (hpos i)
  have hagree : Equiv.refl (Fin 4)=sigma.val := permutations_agree
    (fun i=>(originalSimpleHom K false i).range) (fun i=>(originalSimpleHom K true i).range)
    (by
      rintro i j hij _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
      exact original_distinct_opposite_commute K i j hij a b)
    (fun i=>⟨_,⟨Multiplicative.ofAdd 1,rfl⟩,_,⟨Multiplicative.ofAdd 1,rfl⟩,
      original_same_axis_not_commute K p i⟩) f (Equiv.refl _) sigma.val hp (hsigma true)
  apply eq_one_of_positive_parameters_fixed K p f _ hpos
  intro neg i
  rw [←hagree] at hsigma
  exact hsigma neg i

private theorem eq_of_positive_actions_eq (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (hn:¬IsMulCommutative (Projective CartanMatrix.F₄ K))
    (d e:originalPairNormalizer K p)
    (h:∀i a,d.val*originalSimpleHom K false i (Multiplicative.ofAdd a)*d.val⁻¹=
      e.val*originalSimpleHom K false i (Multiplicative.ofAdd a)*e.val⁻¹) : d=e := by
  let z := e⁻¹*d
  let f := MulAut.conj z.val
  have hU := map_conj_eq _ z.val z.property.1
  have hV := map_conj_eq _ z.val z.property.2
  have hpos (i:Fin 4) (a:K) : f (originalSimpleHom K false i (Multiplicative.ofAdd a))=
      originalSimpleHom K false i (Multiplicative.ofAdd a) := by
    change (e.val⁻¹*d.val)*originalSimpleHom K false i (Multiplicative.ofAdd a)*(e.val⁻¹*d.val)⁻¹=_
    calc
      _=e.val⁻¹*(d.val*originalSimpleHom K false i (Multiplicative.ofAdd a)*d.val⁻¹)*e.val := by group
      _=e.val⁻¹*(e.val*originalSimpleHom K false i (Multiplicative.ofAdd a)*e.val⁻¹)*e.val :=
        congrArg (fun x=>e.val⁻¹*x*e.val) (h i a)
      _=_ := by group
  have hf : f=1 := eq_one_of_pair_and_positive_fixed K p f hU hV hpos
  have hcenter : Subgroup.center (Projective CartanMatrix.F₄ K)=⊥ := by
    rcases (inferInstance : (Subgroup.center (Projective CartanMatrix.F₄ K)).Normal).eq_bot_or_eq_top with hc|hc
    · exact hc
    · exact (hn (Subgroup.center_eq_top_iff.mp hc)).elim
  have hz : z.val∈Subgroup.center (Projective CartanMatrix.F₄ K) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    have he : z.val*x*z.val⁻¹=x := congrArg (fun A:MulAut (Projective CartanMatrix.F₄ K)=>A x) hf
    have hh := congrArg (fun a=>a*z.val) he
    have hc : z.val*x=x*z.val := by
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
    exact hc.symm
  rw [hcenter] at hz
  have hz1 : e.val⁻¹*d.val=1 := Subgroup.mem_bot.mp hz
  exact Subtype.ext (inv_mul_eq_one.mp hz1).symm

theorem originalPairNormalizer_card_le (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (hn:¬IsMulCommutative (Projective CartanMatrix.F₄ K)) :
    Nat.card (originalPairNormalizer K p)≤Nat.card K^4 := by
  letI : Finite (Projective CartanMatrix.F₄ K) := Finite.of_surjective
    (generatedToOriginal K) (generatedToOriginal_surjective K)
  choose c hc using fun d:originalPairNormalizer K p=>
    originalPairNormalizer_positive_scalars K p d.val d.property
  let encode : originalPairNormalizer K p→Fin 4→Kˣ := c
  have hinj : Function.Injective encode := by
    intro d e he
    apply eq_of_positive_actions_eq K p hn d e
    intro i a
    exact (hc d i a).trans (by rw [show c d i=c e i from congrFun he i];exact (hc e i a).symm)
  have hu : Nat.card (Kˣ)≤Nat.card K :=
    Nat.card_le_card_of_injective (fun x:Kˣ=>(x:K)) Units.val_injective
  calc
    Nat.card (originalPairNormalizer K p)≤Nat.card (Fin 4→Kˣ) :=
      Nat.card_le_card_of_injective encode hinj
    _=Nat.card (Kˣ)^4 := by rw [Nat.card_fun,Nat.card_fin]
    _≤Nat.card K^4 := Nat.pow_le_pow_left hu 4

end SymmetricSubgroupAsymptotics.CFSGFFourE6PairNormalizerCardinality
