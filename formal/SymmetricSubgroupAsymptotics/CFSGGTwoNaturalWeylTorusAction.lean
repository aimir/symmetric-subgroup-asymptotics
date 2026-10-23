import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGGTwoShortWeylMatrices

/-! The two literal Weyl words normalize the actual faithful rank-two
torus, with their exact unit-parameter transformations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoNaturalWeylTorusAction
open CFSGGTwoSerreMatrices CFSGGTwoShortWeylMatrices
open CFSGGTwoNaturalRankTwoTorus CFSGGTwoLongTorusAction
variable (K : Type) [Field K]

private theorem vec4_two {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 2 = c := rfl
private theorem vec4_three {R : Type*} (a b c d : R) :
    (![a,b,c,d] : Fin 4 → R) 3 = d := rfl

def shortTransform (t : Kˣ × Kˣ) : Kˣ × Kˣ := (t.2*t.1⁻¹,t.2)
def longTransform (t : Kˣ × Kˣ) : Kˣ × Kˣ := (t.1,t.1^3*t.2⁻¹)

private theorem short_apply (v : Index → K) :
    ((naturalShortWeyl K).val : Mat K) *ᵥ v=shortWeylAction K 1 v := by
  change ((shortWeylParameter K 1).val : Mat K) *ᵥ v=shortWeylAction K 1 v
  exact shortWeylParameter_apply K 1 v

private theorem long_apply (v : Index → K) :
    ((naturalLongWeyl K).val : Mat K) *ᵥ v=weylAction (-1) v := by
  have he : longWeylParameter (-1 : Kˣ)=naturalLongWeyl K := by
    simp [longWeylParameter,naturalLongWeyl]
  rw [←he]
  exact longWeylParameter_apply (-1) v

private theorem short_covariance (t : Kˣ × Kˣ) (v : Index → K) :
    shortWeylAction K 1 (pairAction K t v)=
      pairAction K (shortTransform K t) (shortWeylAction K 1 v) := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [shortWeylAction,pairAction,shortTransform,pos,neg,vec4_two,vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> simp

private theorem long_covariance (t : Kˣ × Kˣ) (v : Index → K) :
    weylAction (-1 : Kˣ) (pairAction K t v)=
      pairAction K (longTransform K t) (weylAction (-1 : Kˣ) v) := by
  funext x
  rcases x with i | i <;> fin_cases i <;>
    simp [weylAction,pairAction,longTransform,pos,neg,vec4_two,vec4_three,
      Units.val_inv_eq_inv_val] <;> field_simp <;> simp

theorem shortWeyl_torusPair (t : Kˣ × Kˣ) :
    naturalShortWeyl K*torusPair K t*(naturalShortWeyl K)⁻¹=
      torusPair K (shortTransform K t) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  change (((naturalShortWeyl K).val : Mat K)*((torusPair K t).val : Mat K)) *ᵥ
      Pi.single i 1 = (((torusPair K (shortTransform K t)).val : Mat K)*
        ((naturalShortWeyl K).val : Mat K)) *ᵥ Pi.single i 1
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,short_apply,torusPair_apply,
    torusPair_apply,short_apply]
  exact short_covariance K t (Pi.single i 1)

theorem longWeyl_torusPair (t : Kˣ × Kˣ) :
    naturalLongWeyl K*torusPair K t*(naturalLongWeyl K)⁻¹=
      torusPair K (longTransform K t) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  change (((naturalLongWeyl K).val : Mat K)*((torusPair K t).val : Mat K)) *ᵥ
      Pi.single i 1 = (((torusPair K (longTransform K t)).val : Mat K)*
        ((naturalLongWeyl K).val : Mat K)) *ᵥ Pi.single i 1
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,long_apply,torusPair_apply,
    torusPair_apply,long_apply]
  exact long_covariance K t (Pi.single i 1)

end SymmetricSubgroupAsymptotics.CFSGGTwoNaturalWeylTorusAction
