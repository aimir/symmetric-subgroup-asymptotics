import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleProductTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarCompatibility
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedWords

/-! All actual fixed torus elements act on the literal fixed middle
word with the Suzuki two-coordinate weights. The computation remains
in the same original F4 Model before any central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedMiddleTorusAction
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalProductTorus
open CFSGFFourOriginalMiddleProductTorusAction
open CFSGFFourRelativeScalarIndex CFSGIntegerMatrixPowerHom
open CFSGReeFFourFieldParameters CFSGReeFFourMiddleFixedWords
open CFSGReeFFourFixedTorus CFSGReeFFourFixedTorusScalarCompatibility

private theorem conjugate_four {G : Type*} [Group G] (g x y z w : G) :
    g*(x*y*z*w)*g⁻¹=(g*x*g⁻¹)*(g*y*g⁻¹)*(g*z*g⁻¹)*(g*w*g⁻¹) := by group

def middleScalar (m : ℕ) (u v : (Field m)ˣ) : (Field m)ˣ :=
  powerHom (G := (Field m)ˣ) relativeCartan (fixedTorusTuple m u v) 1

theorem model_product_torus_middleWord (m : ℕ) (x : Fin 4 → (Field m)ˣ)
    (a b c d : Field m) :
    modelProductTorusHom (Field m) x*middleWord m a b c d*
      (modelProductTorusHom (Field m) x)⁻¹=
    middleWord m (a*(powerHom (G := (Field m)ˣ) relativeCartan x 1 : Field m))
      (b*(powerHom (G := (Field m)ˣ) relativeCartan x 2 : Field m))
      (c*(powerHom (G := (Field m)ˣ) relativeCartan x 1*powerHom (G := (Field m)ˣ) relativeCartan x 2 : (Field m)ˣ))
      (d*((powerHom (G := (Field m)ˣ) relativeCartan x 1)^2*powerHom (G := (Field m)ˣ) relativeCartan x 2 : (Field m)ˣ)) := by
  have h1 := model_product_torus_action (Field m) x false 1 a
  have h2 := model_product_torus_action (Field m) x false 2 b
  simp only [Bool.false_eq_true,if_false] at h1 h2
  unfold middleWord
  rw [conjugate_four,h1,h2,model_product_torus_middleLong,model_product_torus_middleShort]

theorem fixed_torus_middleWord_action (m : ℕ) (u v : (Field m)ˣ) (a c : Field m) :
    (fixedTorus m u v).val*fixedMiddleWord m a c*(fixedTorus m u v).val⁻¹=
      fixedMiddleWord m (a*(middleScalar m u v : Field m))
        (c*((middleScalar m u v : Field m)*alpha m (middleScalar m u v : Field m))) := by
  let s : Field m := middleScalar m u v
  have h := model_product_torus_middleWord m (fixedTorusTuple m u v)
    a (alpha m a) c (alpha m c+a^2*alpha m a)
  rw [fixed_middle_scalar_twist] at h
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,alphaUnits_val] at h
  change (fixedTorus m u v).val*fixedMiddleWord m a c*(fixedTorus m u v).val⁻¹=
    fixedMiddleWord m (a*s) (c*(s*alpha m s))
  calc
    _=middleWord m (a*s) (alpha m a*alpha m s) (c*(s*alpha m s))
        ((alpha m c+a^2*alpha m a)*(s^2*alpha m s)) := h
    _=fixedMiddleWord m (a*s) (c*(s*alpha m s)) := by
      unfold fixedMiddleWord
      congr 1 <;> simp only [map_mul,map_add,map_pow,alpha_twice] <;> ring

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedMiddleTorusAction
