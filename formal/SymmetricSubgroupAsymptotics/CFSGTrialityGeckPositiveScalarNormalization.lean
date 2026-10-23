import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPositiveSemilinear
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! A literal inner torus word removes both positive scalar constants.
The normalized original automorphism still fixes the genuine opposed
pair and acts on the positive charts by unital field automorphisms.
Their common restriction and opposite-sign coupling are not assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveScalarNormalization
open CFSGTrialityGeckOriginalPositiveSemilinear CFSGTrialityGeckOriginalPairScalarAction
open CFSGTrialityGeckOriginalPairNormalizer CFSGTrialityGeckOriginalSimpleParameters
open CFSGTrialityGeckOriginalRootFamily CFSGTrialityGeckOriginalOppositeAlignment
open CFSGTrialityFixedField CFSGSubgroupConjugateOrbitCardinality

def postInner {G:Type*} [Group G] (d:G) (f:MulAut G) : MulAut G := (MulAut.conj d)*f

theorem postInner_apply {G:Type*} [Group G] (d:G) (f:MulAut G) (x:G) :
    postInner d f x=d*f x*d⁻¹ := rfl

private theorem map_after_conj {G:Type*} [Group G] (U:Subgroup G) (f:MulAut G)
    (hf:U.map f.toMonoidHom=U) (d:G) (hd:d∈Subgroup.normalizer (U:Set G)) :
    U.map (postInner d f).toMonoidHom=U := by
  have he : U.map (postInner d f).toMonoidHom=
      (U.map f.toMonoidHom).map (MulAut.conj d).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [he,hf]
  exact conjugate_eq_of_mem_normalizer U d hd

theorem exists_positive_normalized_pair_fixer (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃d∈originalPairNormalizer q,
      ∃sigma:q.Extension 3≃+*q.Extension 3,∃tau:fixedField q≃+*fixedField q,
      ((originalSylow q).map (postInner d f).toMonoidHom=originalSylow q)∧
      ((originalNegative q).map (postInner d f).toMonoidHom=originalNegative q)∧
      (∀t,(postInner d f) (originalShortHom q false (Multiplicative.ofAdd t))=
        originalShortHom q false (Multiplicative.ofAdd (sigma t)))∧
      (∀t:fixedField q,(postInner d f) (originalMiddleHom q false (Multiplicative.ofAdd t))=
        originalMiddleHom q false (Multiplicative.ofAdd (tau t))) := by
  obtain ⟨sigma,tau,c,a,hx,hy⟩ := positive_parameters_semilinear q f hp hn
  obtain ⟨d,hd,hdx,hdy⟩ := originalPairNormalizer_realizes_scalars q c⁻¹ a⁻¹
  refine ⟨d,hd,sigma,tau,map_after_conj _ f hp d hd.1,
    map_after_conj _ f hn d hd.2,?_,?_⟩
  · intro t
    rw [postInner_apply,hx]
    calc
      _=originalShortHom q false (Multiplicative.ofAdd
        (((c⁻¹:(q.Extension 3)ˣ):q.Extension 3)*((c:q.Extension 3)*sigma t))) := hdx _
      _=originalShortHom q false (Multiplicative.ofAdd (sigma t)) := by
        rw [Units.val_inv_eq_inv_val,inv_mul_cancel_left₀ c.ne_zero]
  · intro t
    rw [postInner_apply,hy]
    calc
      _=originalMiddleHom q false (Multiplicative.ofAdd
        (((a⁻¹:(fixedField q)ˣ):fixedField q)*((a:fixedField q)*tau t))) := hdy _
      _=originalMiddleHom q false (Multiplicative.ofAdd (tau t)) := by
        rw [Units.val_inv_eq_inv_val,inv_mul_cancel_left₀ a.ne_zero]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveScalarNormalization
