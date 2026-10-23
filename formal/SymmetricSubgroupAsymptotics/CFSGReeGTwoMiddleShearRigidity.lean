import SymmetricSubgroupAsymptotics.CFSGReeGTwoCentreFixingLayers
import SymmetricSubgroupAsymptotics.CFSGReeGTwoSquareWeightCoordinates
import SymmetricSubgroupAsymptotics.CFSGAdditiveWeightIntertwiners
import SymmetricSubgroupAsymptotics.CFSGSurjectiveGroupHomFactor

/-! The actual middle-coordinate error of a centre-fixing U3
 automorphism is an additive first-coordinate shear. Actual squared
 torus covariance kills this shear by the checked nonlinear weight
 obstruction. No shear is assumed to exist or be additive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoMiddleShearRigidity
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCoordinates CFSGReeGTwoPositiveFirstQuotient
open CFSGReeGTwoPositiveDerivedKernel CFSGReeGTwoPositiveDerived
open CFSGReeGTwoPositiveCentre CFSGReeGTwoCentreFixingLayers
open CFSGReeGTwoSquareWeightCoordinates CFSGSurjectiveGroupHomFactor

def middleErrorHom (m : ℕ) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0) :
    fixedPositiveGroup m →* Multiplicative (Field m) where
  toFun u := Multiplicative.ofAdd (coordinates m (f u) 1-coordinates m u 1)
  map_one' := by
    change Multiplicative.ofAdd (coordinates m (f 1) 1-coordinates m 1 1)=1
    rw [map_one,coordinates_one]
    exact congrArg Multiplicative.ofAdd (sub_self (0 : Field m))
  map_mul' u v := by
    change Multiplicative.ofAdd (coordinates m (f (u*v)) 1-coordinates m (u*v) 1)=
      Multiplicative.ofAdd ((coordinates m (f u) 1-coordinates m u 1)+
        (coordinates m (f v) 1-coordinates m v 1))
    apply congrArg Multiplicative.ofAdd
    rw [map_mul,coordinates_mul,coordinates_mul]
    simp only [productCoordinates,Matrix.cons_val_one,Matrix.cons_val_zero,hfirst]
    ring

theorem firstKernel_le_middleError_ker (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hcentre : ∀d : Field m,f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd d)) :
    firstKernel m≤(middleErrorHom m f (first_fixed m f hcentre)).ker := by
  intro u hu
  have hd : u∈commutator (fixedPositiveGroup m) := by rwa [commutator_eq_firstKernel m hm]
  change Multiplicative.ofAdd (coordinates m (f u) 1-coordinates m u 1)=1
  rw [middle_derived_fixed m f hcentre u hd,sub_self]
  rfl

def middleShear (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hcentre : ∀d : Field m,f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd d)) : Field m→+Field m where
  toFun a := (factorHom (firstHom m) (firstHom_surjective m)
    (middleErrorHom m f (first_fixed m f hcentre))
    (firstKernel_le_middleError_ker m hm f hcentre) (Multiplicative.ofAdd a)).toAdd
  map_zero' := by
    exact congrArg (fun z : Multiplicative (Field m) => z.toAdd) (map_one
      (factorHom (firstHom m) (firstHom_surjective m)
        (middleErrorHom m f (first_fixed m f hcentre))
        (firstKernel_le_middleError_ker m hm f hcentre)))
  map_add' a b := by
    exact congrArg (fun z : Multiplicative (Field m) => z.toAdd) (map_mul
      (factorHom (firstHom m) (firstHom_surjective m)
        (middleErrorHom m f (first_fixed m f hcentre))
        (firstKernel_le_middleError_ker m hm f hcentre)) (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

theorem middleShear_first (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hcentre : ∀d : Field m,f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd d)) (u : fixedPositiveGroup m) :
    middleShear m hm f hcentre (coordinates m u 0)=coordinates m (f u) 1-coordinates m u 1 :=
  congrArg (fun z : Multiplicative (Field m) => z.toAdd)
    (factorHom_apply (firstHom m) (firstHom_surjective m)
      (middleErrorHom m f (first_fixed m f hcentre))
      (firstKernel_le_middleError_ker m hm f hcentre) u)

theorem square_torus_coordinates (m : ℕ) (r : (Field m)ˣ) (u : fixedPositiveGroup m) :
    coordinates m (fixedPositiveTorusAut m ((cubeUnit m r)^2) u)=squareCoordinates m r (coordinates m u) := by
  obtain ⟨x,rfl⟩ := fixedPositiveChart_surjective m u
  rw [torusAut_square_cubeUnit_apply,coordinates_chart,coordinates_chart]

theorem middleShear_square (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hcentre : ∀d : Field m,f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd d))
    (hcomm : ∀t : (Field m)ˣ,∀u : fixedPositiveGroup m,
      f (fixedPositiveTorusAut m (t^2) u)=fixedPositiveTorusAut m (t^2) (f u))
    (a x : Field m) :
    middleShear m hm f hcentre (a*x^2)=middleShear m hm f hcentre a*(x*alpha m x)^2 := by
  by_cases hx : x=0
  · subst x
    simp only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,map_zero]
  · let r : (Field m)ˣ := Units.mk0 x hx
    let u : fixedPositiveGroup m := fixedPositiveChart m ![a,0,0]
    let t := fixedPositiveTorusAut m ((cubeUnit m r)^2)
    have hu0 : coordinates m u 0=a := congrFun (coordinates_chart m ![a,0,0]) 0
    have ht0 : coordinates m (t u) 0=a*x^2 := by
      rw [square_torus_coordinates]
      change coordinates m u 0*x^2=a*x^2
      rw [hu0]
    have he : coordinates m (f (t u)) 1=coordinates m (t (f u)) 1 :=
      congrArg (fun z : fixedPositiveGroup m => coordinates m z 1) (hcomm (cubeUnit m r) u)
    have hj := middleShear_first m hm f hcentre u
    rw [hu0] at hj
    calc
      middleShear m hm f hcentre (a*x^2)=coordinates m (f (t u)) 1-coordinates m (t u) 1 := by
        rw [←ht0]
        exact middleShear_first m hm f hcentre (t u)
      _ = middleShear m hm f hcentre a*(x*alpha m x)^2 := by
        rw [he,square_torus_coordinates,square_torus_coordinates,hj]
        change coordinates m (f u) 1*(x*alpha m x)^2-coordinates m u 1*(x*alpha m x)^2=
          (coordinates m (f u) 1-coordinates m u 1)*(x*alpha m x)^2
        ring

theorem middle_fixed (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hcentre : ∀d : Field m,f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd d))
    (hcomm : ∀t : (Field m)ˣ,∀u : fixedPositiveGroup m,
      f (fixedPositiveTorusAut m (t^2) u)=fixedPositiveTorusAut m (t^2) (f u))
    (u : fixedPositiveGroup m) : coordinates m (f u) 1=coordinates m u 1 := by
  have hcard : 3<Nat.card (Field m) := by
    have hh : 27≤Nat.card (Field m) := by
      rw [field_card]
      exact Nat.pow_le_pow_right (by decide : 0<(3:ℕ)) (by omega : 3≤2*m+1)
    omega
  have hmoved := CFSGAdditiveWeightIntertwiners.exists_moved_of_cube (alpha m) (alpha_twice m) hcard
  have hz := CFSGAdditiveWeightIntertwiners.middle_square_intertwiner_eq_zero
    (alpha m) hmoved (middleShear m hm f hcentre) (middleShear_square m hm f hcentre hcomm)
  have he := middleShear_first m hm f hcentre u
  rw [hz] at he
  exact sub_eq_zero.mp he.symm

end SymmetricSubgroupAsymptotics.CFSGReeGTwoMiddleShearRigidity
