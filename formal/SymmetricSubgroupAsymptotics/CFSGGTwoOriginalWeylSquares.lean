import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRankTwoTorus

/-! Exact square bindings for the two differently oriented ORIGINAL Weyl
words. The short comparison uses the checked staged natural action, not
any ordinary-G2 simplicity or abstract rank-one recognition theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylSquares
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoOriginalRankTwoTorus CFSGGTwoNaturalRankTwoTorus

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 2=c := rfl
private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 3=d := rfl

variable (K : Type) [Field K]

private theorem shortWeyl_apply (v : Index → K) :
    (shortWeyl K : Mat K)*ᵥv=shortWeylAction K 1 v := by
  change ((shortWeylParameter K 1).val:Mat K)*ᵥv=shortWeylAction K 1 v
  exact shortWeylParameter_apply K 1 v

theorem shortWord_square : shortWord K*shortWord K=torusNode K 0 (-1) := by
  apply (modelEquivNatural K).injective
  rw [map_mul,shortWord_native,shortNode_native]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  change ((shortWeyl K:Mat K)*(shortWeyl K:Mat K))*ᵥv=
    ((shortTorus K (-1)).val:Mat K)*ᵥv
  rw [←Matrix.mulVec_mulVec,shortWeyl_apply,shortWeyl_apply,shortTorus_apply]
  funext x
  rcases x with i|i <;> fin_cases i <;>
    simp [shortWeylAction,shortTorusAction,pos,neg,vec4_two,vec4_three,
      Units.val_inv_eq_inv_val]

theorem longWord_square : longWord K*longWord K=torusNode K 1 (-1) := by
  have h : weylParameter K 1 (-1)=longWord K := by
    simp [weylParameter,longWord]
  simp only [torusNode,h]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylSquares
