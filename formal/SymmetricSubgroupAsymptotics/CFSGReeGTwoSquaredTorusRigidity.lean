import SymmetricSubgroupAsymptotics.CFSGReeGTwoCentralShear

/-! An actual U3 automorphism fixing its centre pointwise and commuting
with every actual squared-torus automorphism is the identity. Both
coordinate error shears are constructed from genuine homomorphisms and
eliminated by checked characteristic-three weight identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoSquaredTorusRigidity
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveFirstQuotient CFSGReeGTwoPositiveCentre
open CFSGReeGTwoPositiveDerived CFSGReeGTwoPositiveCube
open CFSGReeGTwoCentreFixingLayers CFSGReeGTwoMiddleShearRigidity
open CFSGReeGTwoCentralShear CFSGReeGTwoSquareWeightCoordinates

theorem centralShear_square (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1)
    (hcomm : ∀t : (Field m)ˣ,∀u : fixedPositiveGroup m,
      f (fixedPositiveTorusAut m (t^2) u)=fixedPositiveTorusAut m (t^2) (f u))
    (a x : Field m) :
    centralShear m hm f hfirst hmiddle (a*x^2)=
      centralShear m hm f hfirst hmiddle a*cubeScalar m (x^2) := by
  by_cases hx : x=0
  · subst x
    simp only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,map_zero,cubeScalar]
  · let r : (Field m)ˣ := Units.mk0 x hx
    let u : fixedPositiveGroup m := fixedPositiveChart m ![a,0,0]
    let t := fixedPositiveTorusAut m ((cubeUnit m r)^2)
    have hu0 : coordinates m u 0=a := congrFun (coordinates_chart m ![a,0,0]) 0
    have ht0 : coordinates m (t u) 0=a*x^2 := by
      rw [square_torus_coordinates]
      change coordinates m u 0*x^2=a*x^2
      rw [hu0]
    have he : coordinates m (f (t u)) 2=coordinates m (t (f u)) 2 :=
      congrArg (fun z : fixedPositiveGroup m => coordinates m z 2) (hcomm (cubeUnit m r) u)
    have hj := centralShear_first m hm f hfirst hmiddle u
    rw [hu0] at hj
    calc
      centralShear m hm f hfirst hmiddle (a*x^2)=
          coordinates m (f (t u)) 2-coordinates m (t u) 2 := by
        rw [←ht0]
        exact centralShear_first m hm f hfirst hmiddle (t u)
      _ = centralShear m hm f hfirst hmiddle a*cubeScalar m (x^2) := by
        rw [he,square_torus_coordinates,square_torus_coordinates,hj]
        change coordinates m (f u) 2*cubeScalar m (x^2)-coordinates m u 2*cubeScalar m (x^2)=
          (coordinates m (f u) 2-coordinates m u 2)*cubeScalar m (x^2)
        ring

theorem last_fixed_of_first_middle (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (hfirst : ∀u : fixedPositiveGroup m,coordinates m (f u) 0=coordinates m u 0)
    (hmiddle : ∀u : fixedPositiveGroup m,coordinates m (f u) 1=coordinates m u 1)
    (hcomm : ∀t : (Field m)ˣ,∀u : fixedPositiveGroup m,
      f (fixedPositiveTorusAut m (t^2) u)=fixedPositiveTorusAut m (t^2) (f u))
    (u : fixedPositiveGroup m) : coordinates m (f u) 2=coordinates m u 2 := by
  have hcard : 3<Nat.card (Field m) := by
    have hh : 27≤Nat.card (Field m) := by
      rw [field_card]
      exact Nat.pow_le_pow_right (by decide : 0<(3:ℕ)) (by omega : 3≤2*m+1)
    omega
  have hmoved := CFSGAdditiveWeightIntertwiners.exists_moved_of_cube (alpha m) (alpha_twice m) hcard
  have hmod : Nat.card (Field m)%4=3 := by
    rw [field_card,pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  have hz := CFSGAdditiveWeightIntertwiners.cube_square_intertwiner_eq_zero hmod (alpha m)
    hmoved (centralShear m hm f hfirst hmiddle)
    (fun a x => centralShear_square m hm f hfirst hmiddle hcomm a x)
  have he := centralShear_first m hm f hfirst hmiddle u
  rw [hz] at he
  exact sub_eq_zero.mp he.symm

theorem eq_one_of_center_fixed_square_torus (m : ℕ) (hm : 1≤m)
    (f : MulAut (fixedPositiveGroup m))
    (hcentre : ∀d : Field m,f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd d))
    (hcomm : ∀t : (Field m)ˣ,∀u : fixedPositiveGroup m,
      f (fixedPositiveTorusAut m (t^2) u)=fixedPositiveTorusAut m (t^2) (f u)) : f=1 := by
  have hf0 (u : fixedPositiveGroup m) : coordinates m (f u) 0=coordinates m u 0 := first_fixed m f hcentre u
  have hf1 (u : fixedPositiveGroup m) : coordinates m (f u) 1=coordinates m u 1 := middle_fixed m hm f hcentre hcomm u
  apply MulEquiv.ext
  intro u
  change f u=u
  apply (fixedPositiveEquiv m).symm.injective
  change coordinates m (f u)=coordinates m u
  funext i
  fin_cases i
  · exact hf0 u
  · exact hf1 u
  · exact last_fixed_of_first_middle m hm f hf0 hf1 hcomm u

end SymmetricSubgroupAsymptotics.CFSGReeGTwoSquaredTorusRigidity
