import SymmetricSubgroupAsymptotics.CFSGGTwoSimpleWeylNegative
import SymmetricSubgroupAsymptotics.CFSGGTwoOrthogonalWeylAxes
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalWeylSquares
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveTorusAction

/-! All twelve actual simple-Weyl actions on the six ORIGINAL positive
root words, with signs and the two negative simple roots retained. The
proof uses definitions, two orthogonal pairs, and literal Weyl-square torus
weights; no Bruhat or root-recognition hypothesis is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleWeylTransport
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalNaturalEquivalence CFSGGTwoOriginalRankTwoTorus
open CFSGGTwoOriginalWeylSquares CFSGGTwoOriginalPositiveTorusAction
open CFSGGTwoNaturalPositiveTorusAction CFSGGTwoOrthogonalWeylAxes
variable (K : Type) [Field K]

private theorem positive_zero (t : K) : positiveModel K 0 t=modelRoot CartanMatrix.G₂ K false 0 t := by
  change 1*modelRoot CartanMatrix.G₂ K false 0 t*1⁻¹=_
  simp only [inv_one,one_mul,mul_one]
private theorem positive_one (t : K) : positiveModel K 1 t=modelRoot CartanMatrix.G₂ K false 1 t := by
  change 1*modelRoot CartanMatrix.G₂ K false 1 t*1⁻¹=_
  simp only [inv_one,one_mul,mul_one]

private theorem conjugate_product {G : Type*} [Group G] (a b x : G) :
    a*(b*x*b⁻¹)*a⁻¹=(a*b)*x*(a*b)⁻¹ := by group

private theorem conjugate_image {G : Type*} [Group G] (s x y z : G)
    (hxy : s*x*s⁻¹=y) (hxz : (s*s)*x*(s*s)⁻¹=z) : s*y*s⁻¹=z := by
  rw [←hxy]
  exact (conjugate_product s s x).trans hxz

private theorem torusNode_one (i : Fin 2) : torusNode K i 1=1 := by
  have h : weylParameter K i (-1)=(weylParameter K i 1)⁻¹ := by
    simp [weylParameter,mul_inv_rev,modelRoot_inv,mul_assoc]
  simp only [torusNode,h,mul_inv_cancel]

private theorem short_square_root (j : Fin 6) (t : K) :
    (shortWord K*shortWord K)*positiveModel K j t*(shortWord K*shortWord K)⁻¹=
      positiveModel K j (t*(rootScale K (-1,1) j:K)) := by
  rw [shortWord_square]
  simpa only [torusPair,torusNode_one,mul_one] using torusPair_positiveModel K (-1,1) j t

private theorem long_square_root (j : Fin 6) (t : K) :
    (longWord K*longWord K)*positiveModel K j t*(longWord K*longWord K)⁻¹=
      positiveModel K j (t*(rootScale K (1,-1) j:K)) := by
  rw [longWord_square]
  simpa only [torusPair,torusNode_one,one_mul] using torusPair_positiveModel K (1,-1) j t

theorem short_one (t : K) :
    shortWord K*positiveModel K 1 t*(shortWord K)⁻¹=positiveModel K 4 t := by
  rw [positive_one]
  rfl

theorem short_two (t : K) :
    shortWord K*positiveModel K 2 t*(shortWord K)⁻¹=positiveModel K 3 t :=
  conjugate_product (shortWord K) (longWord K) (modelRoot CartanMatrix.G₂ K false 0 t)

theorem long_zero (t : K) :
    longWord K*positiveModel K 0 t*(longWord K)⁻¹=positiveModel K 2 t := by
  rw [positive_zero]
  rfl

theorem long_four (t : K) :
    longWord K*positiveModel K 4 t*(longWord K)⁻¹=positiveModel K 5 t :=
  conjugate_product (longWord K) (shortWord K) (modelRoot CartanMatrix.G₂ K false 1 t)

theorem short_three (t : K) :
    shortWord K*positiveModel K 3 t*(shortWord K)⁻¹=positiveModel K 2 (-t) := by
  apply conjugate_image (shortWord K) (positiveModel K 2 t) _ _ (short_two K t)
  simpa [rootScale] using short_square_root K 2 t

theorem short_four (t : K) :
    shortWord K*positiveModel K 4 t*(shortWord K)⁻¹=positiveModel K 1 (-t) := by
  apply conjugate_image (shortWord K) (positiveModel K 1 t) _ _ (short_one K t)
  simpa [rootScale,show (-1:K)^3=(-1:K) by ring] using short_square_root K 1 t

theorem long_two (t : K) :
    longWord K*positiveModel K 2 t*(longWord K)⁻¹=positiveModel K 0 (-t) := by
  apply conjugate_image (longWord K) (positiveModel K 0 t) _ _ (long_zero K t)
  simpa [rootScale] using long_square_root K 0 t

theorem long_five (t : K) :
    longWord K*positiveModel K 5 t*(longWord K)⁻¹=positiveModel K 4 (-t) := by
  apply conjugate_image (longWord K) (positiveModel K 4 t) _ _ (long_four K t)
  simpa [rootScale] using long_square_root K 4 t

theorem short_five (t : K) :
    shortWord K*positiveModel K 5 t*(shortWord K)⁻¹=positiveModel K 5 t := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul,shortWord_native,positiveModel_native,Subgroup.coe_mul] using
    (short_highest_commute K t).eq

theorem long_three (t : K) :
    longWord K*positiveModel K 3 t*(longWord K)⁻¹=positiveModel K 3 t := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul,longWord_native,positiveModel_native,Subgroup.coe_mul] using
    (long_middle_commute K t).eq

/-- Exact signed image; only the omitted simple root is negative. -/
def shortImage (j : Fin 6) (t : K) : Model CartanMatrix.G₂ K :=
  match j.val with
  | 0 => modelRoot CartanMatrix.G₂ K true 0 (-t)
  | 1 => positiveModel K 4 t
  | 2 => positiveModel K 3 t
  | 3 => positiveModel K 2 (-t)
  | 4 => positiveModel K 1 (-t)
  | _ => positiveModel K 5 t

def longImage (j : Fin 6) (t : K) : Model CartanMatrix.G₂ K :=
  match j.val with
  | 0 => positiveModel K 2 t
  | 1 => modelRoot CartanMatrix.G₂ K true 1 (-t)
  | 2 => positiveModel K 0 (-t)
  | 3 => positiveModel K 3 t
  | 4 => positiveModel K 5 t
  | _ => positiveModel K 4 (-t)

theorem short_transport (j : Fin 6) (t : K) :
    shortWord K*positiveModel K j t*(shortWord K)⁻¹=shortImage K j t := by
  fin_cases j
  · exact CFSGGTwoSimpleWeylNegative.short_original K t
  · exact short_one K t
  · exact short_two K t
  · exact short_three K t
  · exact short_four K t
  · exact short_five K t

theorem long_transport (j : Fin 6) (t : K) :
    longWord K*positiveModel K j t*(longWord K)⁻¹=longImage K j t := by
  fin_cases j
  · exact long_zero K t
  · exact CFSGGTwoSimpleWeylNegative.long_original K t
  · exact long_two K t
  · exact long_three K t
  · exact long_four K t
  · exact long_five K t

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalSimpleWeylTransport
