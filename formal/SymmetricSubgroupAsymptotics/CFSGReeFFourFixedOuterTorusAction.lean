import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarCompatibility
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusAction

/-! Every element of the genuine two-unit fixed torus acts by a scalar
on the literal outer fixed root group, and on its faithful image in the
same original Ree central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterTorusAction
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus
open CFSGReeFFourFixedTorusScalarCompatibility CFSGFFourOriginalProductTorus
open CFSGFFourRelativeScalarIndex CFSGIntegerMatrixPowerHom
open CFSGReeFFourOuterFixedRoot CFSGReeFFourOuterTorusAction CFSGReeFFourPerfectProjection

def outerScalar (m : ℕ) (u v : (Field m)ˣ) : (Field m)ˣ :=
  powerHom (G := (Field m)ˣ) relativeCartan (fixedTorusTuple m u v) 0

theorem model_fixed_torus_outerWord_action (m : ℕ) (u v : (Field m)ˣ) (a : Field m) :
    (fixedTorus m u v).val*outerWord m a*(fixedTorus m u v).val⁻¹=
      outerWord m (a*(outerScalar m u v : Field m)) := by
  let D : Model CartanMatrix.F₄ (Field m) :=
    modelProductTorusHom (Field m) (fixedTorusTuple m u v)
  let r : Field m := outerScalar m u v
  have hr3 : (powerHom (G := (Field m)ˣ) relativeCartan (fixedTorusTuple m u v) 3 : Field m)=alpha m r := by
    rw [fixed_outer_scalar_twist,alphaUnits_val]
    rfl
  have h0 : D*modelRoot CartanMatrix.F₄ (Field m) false 0 a*D⁻¹=
      modelRoot CartanMatrix.F₄ (Field m) false 0 (a*r) := by
    simpa only [Bool.false_eq_true,if_false] using
      model_product_torus_action (Field m) (fixedTorusTuple m u v) false 0 a
  have h3 : D*modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m a)*D⁻¹=
      modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m a*alpha m r) := by
    simpa only [Bool.false_eq_true,if_false,hr3] using
      model_product_torus_action (Field m) (fixedTorusTuple m u v) false 3 (alpha m a)
  change D*(modelRoot CartanMatrix.F₄ (Field m) false 0 a*
    modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m a))*D⁻¹=
    modelRoot CartanMatrix.F₄ (Field m) false 0 (a*r)*
      modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m (a*r))
  calc
    _=(D*modelRoot CartanMatrix.F₄ (Field m) false 0 a*D⁻¹)*
        (D*modelRoot CartanMatrix.F₄ (Field m) false 3 (alpha m a)*D⁻¹) := by group
    _=_ := by rw [h0,h3,map_mul]

theorem fixed_torus_outer_parameter_action (m : ℕ) (u v : (Field m)ˣ) (a : Field m) :
    fixedTorus m u v*fixedOuterHom m (Multiplicative.ofAdd a)*(fixedTorus m u v)⁻¹=
      fixedOuterHom m (Multiplicative.ofAdd (a*(outerScalar m u v : Field m))) :=
  Subtype.ext (model_fixed_torus_outerWord_action m u v a)

theorem original_fixed_torus_outer_action (m : ℕ) (hm : 0<m)
    (u v : (Field m)ˣ) (a : Field m) :
    fixedToOriginal m hm (fixedTorus m u v)*originalOuterHom m hm (Multiplicative.ofAdd a)*
      (fixedToOriginal m hm (fixedTorus m u v))⁻¹=
    originalOuterHom m hm (Multiplicative.ofAdd (a*(outerScalar m u v : Field m))) := by
  simpa only [map_mul,map_inv] using congrArg (fixedToOriginal m hm)
    (fixed_torus_outer_parameter_action m u v a)

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterTorusAction
