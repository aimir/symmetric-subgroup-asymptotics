import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeOuterCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterRankOneConstraint
import SymmetricSubgroupAsymptotics.CFSGCentralRootNegativeOneRigidity

/-! Positive one fixes negative one on the actual original outer block.
The original quotient relation is reflected by the proved central-kernel
p-element lemma and the actual positive Sylow injection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterNegativeOne
open CFSGReeFFourOriginalNegativeOuterCoordinates CFSGReeFFourOuterRankOneConstraint
open CFSGReeFFourOuterSignedConjugation CFSGReeFFourOuterTorusReflection
open CFSGReeFFourOuterFixedRoot CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourPerfectProjection CFSGReeFFourOuterTorusAction
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedPositiveSylow
open CFSGReeFFourOriginalNegativeRootIntersections CFSGReeFFourOriginalMiddleParabolic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem hom_two_element {K G : Type*} [Field K] [CharP K 2] [Group G]
    (X : Multiplicative K→*G) (t : Multiplicative K) : ∃k : ℕ,X t^(2^k)=1 := by
  have ht : t^2=1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    exact CharTwo.add_self_eq_zero t.toAdd
  refine ⟨1,?_⟩
  rw [pow_one,←map_pow,ht,map_one]

private theorem source_outer_word (m : ℕ) :
    fixedOuterHom m (Multiplicative.ofAdd 1)*
      fixedNegativeOuterHom m (Multiplicative.ofAdd (-1))*fixedOuterHom m (Multiplicative.ofAdd 1)=
        outerFixedReflection m := by
  rw [fixedNegativeOuterHom_value]
  have he : fixedOuterWeyl m 1=outerFixedReflection m := Subtype.ext (fixedOuterWeyl_one_val m)
  simpa only [fixedOuterWeyl,Units.val_one,inv_one] using he

private theorem source_outer_intertwines (m : ℕ) :
    (fixedOuterHom m (Multiplicative.ofAdd 1)*fixedNegativeOuterHom m (Multiplicative.ofAdd (-1))*
        fixedOuterHom m (Multiplicative.ofAdd 1))*fixedOuterHom m (Multiplicative.ofAdd 1)*
      (fixedOuterHom m (Multiplicative.ofAdd 1)*fixedNegativeOuterHom m (Multiplicative.ofAdd (-1))*
        fixedOuterHom m (Multiplicative.ofAdd 1))⁻¹=
          fixedNegativeOuterHom m (Multiplicative.ofAdd (-1)) := by
  have he := congrArg (fun w : originalModelFixed m=>
    w*fixedOuterHom m (Multiplicative.ofAdd 1)*w⁻¹) (source_outer_word m)
  have hy : fixedSignedOuter m true 1=fixedNegativeOuterHom m (Multiplicative.ofAdd (-1)) := by
    rw [fixedNegativeOuterHom_value]
    simp only [toAdd_ofAdd,CharTwo.neg_eq]
  exact he.trans ((fixed_outer_conjugates_parameter m 1).trans hy)

theorem negative_outer_one_fixed (m : ℕ) (hm : 0<m) (f : MulAut (CFSG.Models.ReeF4 m))
    (hnegative : (originalNegativeRootBlock m hm false).map f.toMonoidHom=
      originalNegativeRootBlock m hm false)
    (hpositive : f (originalOuterHom m hm (Multiplicative.ofAdd 1))=
      originalOuterHom m hm (Multiplicative.ofAdd 1)) :
    f (originalNegativeOuterHom m hm (Multiplicative.ofAdd (-1)))=
      originalNegativeOuterHom m hm (Multiplicative.ofAdd (-1)) := by
  let P := fixedPositiveSylow m
  have hP : Function.Injective ((fixedToOriginal m hm).comp
      (P : Subgroup (originalModelFixed m)).subtype) := by
    intro x y he
    have hx : x.val∈fixedPositive m := by
      simpa only [P,fixedPositiveSylow_coe] using x.property
    have hy : y.val∈fixedPositive m := by
      simpa only [P,fixedPositiveSylow_coe] using y.property
    have hh : ((fixedToOriginal m hm).comp (fixedPositive m).subtype) ⟨x.val,hx⟩=
        ((fixedToOriginal m hm).comp (fixedPositive m).subtype) ⟨y.val,hy⟩ := he
    exact Subtype.ext (congrArg (fun z : fixedPositive m=>z.val)
      (fixedToOriginal_positive_injective m hm hh))
  have hY : ((fixedToOriginal m hm).comp (fixedNegativeOuterHom m)).range.map f.toMonoidHom=
      ((fixedToOriginal m hm).comp (fixedNegativeOuterHom m)).range := by
    change (originalNegativeOuterHom m hm).range.map f.toMonoidHom=(originalNegativeOuterHom m hm).range
    rw [originalNegativeOuterHom_range]
    exact hnegative
  apply CFSGCentralRootNegativeOneRigidity.negative_one_fixed (fixedToOriginal m hm) P hP
    (fixedToOriginal_kernel_le_center m hm) (fixedOuterHom m) (fixedNegativeOuterHom m)
    (originalNegativeOuterHom_injective m hm) (hom_two_element (fixedOuterHom m))
    (hom_two_element (fixedNegativeOuterHom m)) (source_outer_intertwines m) _ f hY hpositive
  intro b hb hinter
  have he := congrArg (fun g : originalModelFixed m=>g.val) hinter
  simp only [Subgroup.coe_mul,fixedNegativeOuterHom_value] at he
  change (signedOuterWord m false 1*signedOuterWord m true b*signedOuterWord m false 1)*
      signedOuterWord m false 1=signedOuterWord m true b*
        (signedOuterWord m false 1*signedOuterWord m true b*signedOuterWord m false 1) at he
  have hc := model_outer_inverse_constraint m 1 b 1 b hb he
  linear_combination hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterNegativeOne
