import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedClassification

/-! Multiplication and inverse of the literal original four-coordinate
middle words. This supplies closure without identifying a full positive
subgroup or passing through a derived or central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWordMultiplication
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalMiddleLongCentrality
open CFSGFFourOriginalMiddleParameterHoms CFSGReeFFourMiddleCentrality
open CFSGReeFFourMiddleCollecting CFSGReeFFourMiddleFixedWords CFSGReeFFourFieldParameters
local notation "A" => CartanMatrix.F₄

private theorem higher_product (m : ℕ) (r s v u : Field m) :
    (middleLong (Field m) r*middleShort (Field m) s)*
      (middleLong (Field m) v*middleShort (Field m) u)=
    middleLong (Field m) (r+v)*middleShort (Field m) (s+u) := by
  have h := (middleLong_commute_middleShort m v s).eq.symm
  calc
    _=middleLong (Field m) r*(middleShort (Field m) s*middleLong (Field m) v)*
      middleShort (Field m) u := by group
    _=middleLong (Field m) r*(middleLong (Field m) v*middleShort (Field m) s)*
      middleShort (Field m) u := by rw [h]
    _=(middleLong (Field m) r*middleLong (Field m) v)*
      (middleShort (Field m) s*middleShort (Field m) u) := by group
    _=_ := by rw [←middleLong_add,←middleShort_add]

theorem middleWord_mul (m : ℕ) (a b c d e f s t : Field m) :
    middleWord m a b c d*middleWord m e f s t=
      middleWord m (a+e) (b+f) (c+s+e*b) (d+t+e^2*b) := by
  have hx := (middleLong_commute_one (Field m) d e).mul_left (middleShort_commute_one m c e)
  have hy := (middleLong_commute_two (Field m) d f).mul_left (middleShort_commute_two m c f)
  have hc := hx.mul_right hy
  have hfront := (middleLong_commute_one (Field m) (e^2*b) a).mul_left
    (middleShort_commute_one m (e*b) a)
  unfold middleWord
  calc
    _=(modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b)*
      ((middleLong (Field m) d*middleShort (Field m) c)*
        (modelRoot A (Field m) false 1 e*modelRoot A (Field m) false 2 f))*
      (middleLong (Field m) t*middleShort (Field m) s) := by group
    _=(modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 2 b)*
      ((modelRoot A (Field m) false 1 e*modelRoot A (Field m) false 2 f)*
        (middleLong (Field m) d*middleShort (Field m) c))*
      (middleLong (Field m) t*middleShort (Field m) s) := by rw [hc.eq]
    _=modelRoot A (Field m) false 1 a*
      (modelRoot A (Field m) false 2 b*modelRoot A (Field m) false 1 e)*
      modelRoot A (Field m) false 2 f*
      ((middleLong (Field m) d*middleShort (Field m) c)*
        (middleLong (Field m) t*middleShort (Field m) s)) := by group
    _=modelRoot A (Field m) false 1 a*
      ((middleLong (Field m) (e^2*b)*middleShort (Field m) (e*b))*
        modelRoot A (Field m) false 1 e*modelRoot A (Field m) false 2 b)*
      modelRoot A (Field m) false 2 f*
      (middleLong (Field m) (d+t)*middleShort (Field m) (c+s)) := by
        rw [middle_reverse_axes,higher_product]
    _=(modelRoot A (Field m) false 1 a*
        (middleLong (Field m) (e^2*b)*middleShort (Field m) (e*b)))*
      ((modelRoot A (Field m) false 1 e*modelRoot A (Field m) false 2 b)*
        modelRoot A (Field m) false 2 f)*
      (middleLong (Field m) (d+t)*middleShort (Field m) (c+s)) := by group
    _=((middleLong (Field m) (e^2*b)*middleShort (Field m) (e*b))*
        modelRoot A (Field m) false 1 a)*
      ((modelRoot A (Field m) false 1 e*modelRoot A (Field m) false 2 b)*
        modelRoot A (Field m) false 2 f)*
      (middleLong (Field m) (d+t)*middleShort (Field m) (c+s)) := by rw [←hfront.eq]
    _=(middleLong (Field m) (e^2*b)*middleShort (Field m) (e*b))*
      ((modelRoot A (Field m) false 1 a*modelRoot A (Field m) false 1 e)*
        (modelRoot A (Field m) false 2 b*modelRoot A (Field m) false 2 f))*
      (middleLong (Field m) (d+t)*middleShort (Field m) (c+s)) := by group
    _=(middleLong (Field m) (e^2*b)*middleShort (Field m) (e*b))*
      (modelRoot A (Field m) false 1 (a+e)*modelRoot A (Field m) false 2 (b+f))*
      (middleShort (Field m) (c+s)*middleLong (Field m) (d+t)) := by
        rw [←source_root_add,←source_root_add,(middleLong_commute_middleShort m (d+t) (c+s)).eq]
    _=modelRoot A (Field m) false 1 (a+e)*modelRoot A (Field m) false 2 (b+f)*
      middleLong (Field m) (e^2*b+(d+t))*middleShort (Field m) (e*b+(c+s)) :=
        middle_collect_central m (a+e) (b+f) (e^2*b) (e*b) (c+s) (d+t)
    _=_ := by rw [add_comm (e^2*b) (d+t),add_comm (e*b) (c+s)]

theorem middleWord_zero (m : ℕ) : middleWord m 0 0 0 0=1 := by
  have hr : middleLong (Field m) 0=1 := (middleLongHom (Field m)).map_one
  have hp : middleShort (Field m) 0=1 := (middleShortHom (Field m)).map_one
  simp only [middleWord,source_root_zero,hr,hp,mul_one]

theorem middleWord_inv (m : ℕ) (a b c d : Field m) :
    (middleWord m a b c d)⁻¹=middleWord m a b (c+a*b) (d+a^2*b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [middleWord_mul]
  have hc : c+(c+a*b)+a*b=0 := by
    rw [←add_assoc c c,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  have hparamd : d+(d+a^2*b)+a^2*b=0 := by
    rw [←add_assoc d d,CharTwo.add_self_eq_zero,zero_add,CharTwo.add_self_eq_zero]
  rw [CharTwo.add_self_eq_zero a,CharTwo.add_self_eq_zero b,hc,hparamd,middleWord_zero]

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWordMultiplication
