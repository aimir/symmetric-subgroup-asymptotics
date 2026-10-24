import SymmetricSubgroupAsymptotics.CFSGReeFFourPerfectProjection
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalars
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusGroup

/-! Actual outer root conjugation by the fixed torus, and its faithful
passage to the pinned original Ree derived/full-centre quotient. The
positive parameter is scaled by a square; squaring on the field units
is already proved onto. No ordinary F4 simplicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusAction
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourPerfectProjection CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOuterFixedRoot CFSGReeFFourFixedTorusGroup
open CFSGReeFFourFixedTorus CFSGReeFFourFixedTorusScalars
open CFSGReeFFourParameterizedTorusCovariance CFSGFFourOriginalProductTorus
open CFSGSerreModelRootGeneration CFSGFFourRelativeScalarIndex CFSG.Models.Chevalley
open CFSGIntegerMatrixPowerHom

private theorem outer_scalar_first (m : ℕ) (a : (Field m)ˣ) :
    ((powerHom (G:=(Field m)ˣ) relativeCartan (fixedTorusTuple m a 1) 0 :
      (Field m)ˣ) : Field m)=(a : Field m)^2 := by
  rw [fixed_torus_scalars]
  change ((a^2 : (Field m)ˣ) : Field m)=(a : Field m)^2
  exact Units.val_pow_eq_pow_val a 2

private theorem outer_scalar_last (m : ℕ) (a : (Field m)ˣ) :
    ((powerHom (G:=(Field m)ˣ) relativeCartan (fixedTorusTuple m a 1) 3 :
      (Field m)ˣ) : Field m)=(alpha m (a : Field m))^2 := by
  rw [fixed_torus_scalars]
  change (((unitPower m 0 a)^2 : (Field m)ˣ) : Field m)=_
  rw [Units.val_pow_eq_pow_val,unitPower_val]
  rfl

private theorem model_torus_outer_action (m : ℕ) (a : (Field m)ˣ) (t : Field m) :
    modelProductTorusHom (Field m) (fixedTorusTuple m a 1)*outerWord m t*
      (modelProductTorusHom (Field m) (fixedTorusTuple m a 1))⁻¹=
        outerWord m (t*(a : Field m)^2) := by
  let D : Model CartanMatrix.F₄ (Field m) :=
    modelProductTorusHom (Field m) (fixedTorusTuple m a 1)
  have h0 : D*modelRoot CartanMatrix.F₄ (Field m) false 0 t*D⁻¹=
      modelRoot CartanMatrix.F₄ (Field m) false 0 (t*(a : Field m)^2) := by
    simpa only [Bool.false_eq_true,if_false,outer_scalar_first] using
      model_product_torus_action (Field m) (fixedTorusTuple m a 1) false 0 t
  have h3 : D*modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m t)*D⁻¹=
      modelRoot CartanMatrix.F₄ (Field m) false 3
        (alpha m t*(alpha m (a : Field m))^2) := by
    simpa only [Bool.false_eq_true,if_false,outer_scalar_last] using
      model_product_torus_action (Field m) (fixedTorusTuple m a 1) false 3 (alpha m t)
  change D*(modelRoot CartanMatrix.F₄ (Field m) false 0 t*
      modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m t))*D⁻¹=
    modelRoot CartanMatrix.F₄ (Field m) false 0 (t*(a : Field m)^2)*
      modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m (t*(a : Field m)^2))
  calc
    _=(D*modelRoot CartanMatrix.F₄ (Field m) false 0 t*D⁻¹)*
        (D*modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m t)*D⁻¹) := by group
    _=_ := by rw [h0,h3,map_mul,map_pow]

theorem fixed_torus_outer_action (m : ℕ) (a : (Field m)ˣ) (t : Field m) :
    fixedTorusHom m (a,1)*fixedOuterHom m (Multiplicative.ofAdd t)*
      (fixedTorusHom m (a,1))⁻¹=
        fixedOuterHom m (Multiplicative.ofAdd (t*(a : Field m)^2)) :=
  Subtype.ext (model_torus_outer_action m a t)

private def positiveOuterHom (m : ℕ) :
    Multiplicative (Field m)→*fixedPositive m :=
  (fixedOuterHom m).codRestrict (fixedPositive m)
    (fun a=>fixedOuterHom_range_le_fixedPositive m ⟨a,rfl⟩)

private theorem positiveOuterHom_injective (m : ℕ) :
    Function.Injective (positiveOuterHom m) := by
  intro a b he
  apply fixedOuterHom_injective m
  exact congrArg (fun z : fixedPositive m=>z.val) he

def originalOuterHom (m : ℕ) (hm : 0<m) :
    Multiplicative (Field m)→*CFSG.Models.ReeF4 m :=
  (fixedToOriginal m hm).comp (fixedOuterHom m)

theorem originalOuterHom_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (originalOuterHom m hm) := by
  intro a b hab
  change fixedToOriginal m hm (fixedOuterHom m a)=
    fixedToOriginal m hm (fixedOuterHom m b) at hab
  have hp : positiveOuterHom m a=positiveOuterHom m b := by
    apply fixedToOriginal_positive_injective m hm
    exact hab
  exact positiveOuterHom_injective m hp

def originalOuterTorus (m : ℕ) (hm : 0<m) (a : (Field m)ˣ) : CFSG.Models.ReeF4 m :=
  fixedToOriginal m hm (fixedTorusHom m (a,1))

theorem original_torus_outer_action (m : ℕ) (hm : 0<m) (a : (Field m)ˣ)
    (t : Field m) :
    originalOuterTorus m hm a*originalOuterHom m hm (Multiplicative.ofAdd t)*
      (originalOuterTorus m hm a)⁻¹=
        originalOuterHom m hm (Multiplicative.ofAdd (t*(a : Field m)^2)) := by
  change fixedToOriginal m hm (fixedTorusHom m (a,1))*
      fixedToOriginal m hm (fixedOuterHom m (Multiplicative.ofAdd t))*
        (fixedToOriginal m hm (fixedTorusHom m (a,1)))⁻¹=
    fixedToOriginal m hm (fixedOuterHom m (Multiplicative.ofAdd (t*(a : Field m)^2)))
  simpa only [map_mul,map_inv] using
    congrArg (fixedToOriginal m hm) (fixed_torus_outer_action m a t)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusAction
