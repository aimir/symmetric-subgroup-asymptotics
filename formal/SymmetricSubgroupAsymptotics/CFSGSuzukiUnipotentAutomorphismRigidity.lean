import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentTorusAction
import SymmetricSubgroupAsymptotics.CFSGSuzukiCentralWeightRigidity

/-! An endomorphism of the actual U which fixes the first quotient and
commutes with the original torus is the identity. Squares fix its actual
central subgroup; multiplicativity makes the remaining shear additive,
and the two literal torus weights force that shear to vanish. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters

def secondParameter (m : ℕ) (g : unipotentSubgroup m) : Field m :=
  (g.val : CFSG.Models.SuzukiConstruction.Mat m) 2 0

@[simp] theorem secondParameter_coordinateElement (m : ℕ) (a b : Field m) :
    secondParameter m (coordinateElement m a b)=b := rfl

theorem coordinateElement_parameters (m : ℕ) (g : unipotentSubgroup m) :
    g=coordinateElement m (firstParameter m g) (secondParameter m g) := by
  obtain ⟨a,b,hg⟩ := g.property
  have he : g=coordinateElement m a b := Subtype.ext hg
  rw [he]
  rfl

theorem coordinateElement_square (m : ℕ) (a b : Field m) :
    coordinateElement m a b*coordinateElement m a b=
      coordinateElement m 0 (theta m a*a) := by
  rw [coordinateElement_mul]
  simp only [CharTwo.add_self_eq_zero,zero_add]

theorem square_eq_firstParameter (m : ℕ) (g : unipotentSubgroup m) :
    g*g=coordinateElement m 0 (theta m (firstParameter m g)*firstParameter m g) := by
  rw [coordinateElement_parameters m g]
  exact coordinateElement_square m _ _

theorem fixes_center_of_fixes_first (m : ℕ)
    (f : unipotentSubgroup m→*unipotentSubgroup m)
    (hf : ∀ g,firstParameter m (f g)=firstParameter m g) (b : Field m) :
    f (coordinateElement m 0 b)=coordinateElement m 0 b := by
  obtain ⟨a,ha⟩ := (thetaProduct_bijective m).surjective b
  have ha' : theta m a*a=b := by simpa only [thetaProduct,mul_comm] using ha
  calc
    f (coordinateElement m 0 b)=f (coordinateElement m a 0*coordinateElement m a 0) := by
      rw [coordinateElement_square,ha']
    _=f (coordinateElement m a 0)*f (coordinateElement m a 0) := map_mul f _ _
    _=coordinateElement m 0 b := by
      rw [square_eq_firstParameter,hf,firstParameter_coordinateElement,ha']

/-- A concrete additive shear on the original parameter field; it is
extracted from an actual group endomorphism, not supplied as classification data. -/
def firstTrivialShear (m : ℕ) (f : unipotentSubgroup m→*unipotentSubgroup m)
    (hf : ∀ g,firstParameter m (f g)=firstParameter m g) : Field m→+Field m where
  toFun a := secondParameter m (f (coordinateElement m a 0))
  map_zero' := by
    rw [coordinateElement_zero,map_one]
    rfl
  map_add' a c := by
    have hshape : ∀ x y : Field m,f (coordinateElement m x y)=
        coordinateElement m x (secondParameter m (f (coordinateElement m x 0))+y) := by
      intro x y
      have hd : coordinateElement m x y=coordinateElement m x 0*coordinateElement m 0 y := by
        rw [coordinateElement_mul]
        simp only [add_zero,mul_zero,zero_add]
      rw [hd,map_mul,fixes_center_of_fixes_first m f hf]
      have he := coordinateElement_parameters m (f (coordinateElement m x 0))
      rw [hf,firstParameter_coordinateElement] at he
      rw [he,coordinateElement_mul]
      simp only [add_zero,mul_zero,secondParameter_coordinateElement]
    have he := congrArg (secondParameter m) (map_mul f (coordinateElement m a 0) (coordinateElement m c 0))
    simp only [coordinateElement_mul,zero_add,add_zero] at he
    rw [hshape (a+c) (theta m a*c),hshape a 0,hshape c 0,coordinateElement_mul] at he
    simp only [secondParameter_coordinateElement,add_zero] at he
    exact add_right_cancel he

theorem firstTrivialShear_shape (m : ℕ)
    (f : unipotentSubgroup m→*unipotentSubgroup m)
    (hf : ∀ g,firstParameter m (f g)=firstParameter m g) (a b : Field m) :
    f (coordinateElement m a b)=coordinateElement m a (firstTrivialShear m f hf a+b) := by
  have hd : coordinateElement m a b=coordinateElement m a 0*coordinateElement m 0 b := by
    rw [coordinateElement_mul]
    simp only [add_zero,mul_zero,zero_add]
  rw [hd,map_mul,fixes_center_of_fixes_first m f hf]
  have he := coordinateElement_parameters m (f (coordinateElement m a 0))
  rw [hf,firstParameter_coordinateElement] at he
  rw [he,coordinateElement_mul]
  simp only [add_zero,mul_zero]
  rfl

theorem firstTrivialShear_weight (m : ℕ)
    (f : unipotentSubgroup m→*unipotentSubgroup m)
    (hf : ∀ g,firstParameter m (f g)=firstParameter m g)
    (hT : ∀ (c : (Field m)ˣ) (g : unipotentSubgroup m),
      f (torusAction m c g)=torusAction m c (f g)) (x : Field m) :
    firstTrivialShear m f hf x=thetaProduct m x*firstTrivialShear m f hf 1 := by
  by_cases hx : x=0
  · subst x
    simp only [map_zero,thetaProduct,zero_mul]
  · let c : (Field m)ˣ := Units.mk0 x hx
    have he := congrArg (secondParameter m) (hT c⁻¹ (coordinateElement m 1 0))
    rw [torusAction_coordinateElement,firstTrivialShear_shape,
      firstTrivialShear_shape,torusAction_coordinateElement] at he
    simp only [secondParameter_coordinateElement,Units.val_inv_eq_inv_val,map_inv₀,
      mul_inv_rev,inv_inv,mul_one,mul_zero,add_zero] at he
    simpa only [c,Units.val_mk0,thetaProduct,mul_comm] using he

/-- Intrinsic rigidity of the actual root group once its first layer and
original torus action have been fixed. No split/model isomorphism is assumed. -/
theorem endomorphism_eq_id_of_first_and_torus (m : ℕ) (hm : 1≤m)
    (f : unipotentSubgroup m→*unipotentSubgroup m)
    (hf : ∀ g,firstParameter m (f g)=firstParameter m g)
    (hT : ∀ (c : (Field m)ˣ) (g : unipotentSubgroup m),
      f (torusAction m c g)=torusAction m c (f g)) : f=MonoidHom.id _ := by
  have hd : firstTrivialShear m f hf=0 :=
    additive_thetaProduct_weight_eq_zero m hm _ (firstTrivialShear_weight m f hf hT)
  apply MonoidHom.ext
  intro g
  obtain ⟨a,b,hg⟩ := g.property
  have he : g=coordinateElement m a b := Subtype.ext hg
  rw [he,firstTrivialShear_shape m f hf,hd]
  simp only [AddMonoidHom.zero_apply,zero_add,MonoidHom.id_apply]

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
