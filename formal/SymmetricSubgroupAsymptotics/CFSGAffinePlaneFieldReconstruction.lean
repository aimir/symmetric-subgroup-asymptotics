import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The field operations are forced by two explicit affine-plane
incidence configurations. This is the algebraic part of a normalized
projective-frame reconstruction, not a global automorphism assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAffinePlaneFieldReconstruction
variable {F : Type*} [Field F]

def Collinear (p q r : F×F) : Prop :=
  (q.1-p.1)*(r.2-p.2)=(q.2-p.2)*(r.1-p.1)

def coordinateMap (s : F≃F) (p : F×F) : F×F := (s p.1,s p.2)

theorem map_mul_of_collinear (s : F≃F) (h0 : s 0=0) (h1 : s 1=1)
    (hcol : ∀ p q r,Collinear p q r→
      Collinear (coordinateMap s p) (coordinateMap s q) (coordinateMap s r))
    (a b : F) : s (a*b)=s a*s b := by
  have hc : Collinear (0,0) (1,a) (b,a*b) := by
    unfold Collinear
    dsimp only
    ring
  have hh := hcol _ _ _ hc
  simpa [Collinear,coordinateMap,h0,h1] using hh

theorem map_complement_of_collinear (s : F≃F) (h0 : s 0=0) (h1 : s 1=1)
    (hcol : ∀ p q r,Collinear p q r→
      Collinear (coordinateMap s p) (coordinateMap s q) (coordinateMap s r))
    (a : F) : s (1-a)=1-s a := by
  have hc : Collinear (1,0) (0,1) (a,1-a) := by
    unfold Collinear
    dsimp only
    ring
  have hh := hcol _ _ _ hc
  have he : -s (1-a)=s a-1 := by
    simpa [Collinear,coordinateMap,h0,h1] using hh
  apply neg_injective
  rw [he]
  ring

private theorem map_neg_one (s : F≃F) (h1 : s 1=1)
    (hmul : ∀ a b,s (a*b)=s a*s b) : s (-1)=-1 := by
  have hs : s (-1)*s (-1)=1 := by
    rw [←hmul,neg_one_mul,neg_neg,h1]
  have hp : (s (-1)-1)*(s (-1)+1)=0 := by
    calc
      _=s (-1)*s (-1)-1 := by ring
      _=0 := by rw [hs,sub_self]
  rcases mul_eq_zero.mp hp with hm | hp
  · have hm' : s (-1)=1 := sub_eq_zero.mp hm
    have hh : (-1 : F)=1 := s.injective (hm'.trans h1.symm)
    exact hm'.trans hh.symm
  · have hh := congrArg (fun z : F => z-1) hp
    simpa only [add_sub_cancel_right,zero_sub] using hh

private theorem map_add_of_mul_complement (s : F≃F) (h0 : s 0=0) (h1 : s 1=1)
    (hmul : ∀ a b,s (a*b)=s a*s b) (hcomp : ∀ a,s (1-a)=1-s a)
    (x y : F) : s (x+y)=s x+s y := by
  let h : F→*₀F := { toFun := s, map_zero' := h0, map_one' := h1, map_mul' := hmul }
  have hneg (a : F) : s (-a)=-s a := by
    rw [show -a=(-1)*a by ring,hmul,map_neg_one s h1 hmul,neg_one_mul]
  have hsub (a b : F) : s (a-b)=s a-s b := by
    by_cases ha : a=0
    · subst a
      simp only [zero_sub,hneg,h0]
    · have hsa : s a≠0 := by
        intro he
        exact ha (s.injective (he.trans h0.symm))
      have he : a-b=a*(1-b/a) := by field_simp [ha]
      rw [he,hmul,hcomp]
      have hdiv : s (b/a)=s b/s a := map_div₀ h b a
      rw [hdiv]
      field_simp [hsa]
      <;> ring
  rw [show x+y=x-(-y) by ring,hsub,hneg,sub_neg_eq_add]

def ringAutOfCoordinateCollinearity (s : F≃F) (h0 : s 0=0) (h1 : s 1=1)
    (hcol : ∀ p q r,Collinear p q r→
      Collinear (coordinateMap s p) (coordinateMap s q) (coordinateMap s r)) : F≃+*F :=
  { s with
    map_mul' := map_mul_of_collinear s h0 h1 hcol
    map_add' := map_add_of_mul_complement s h0 h1
      (map_mul_of_collinear s h0 h1 hcol) (map_complement_of_collinear s h0 h1 hcol) }

@[simp] theorem ringAutOfCoordinateCollinearity_apply (s : F≃F) (h0 : s 0=0) (h1 : s 1=1)
    (hcol : ∀ p q r,Collinear p q r→
      Collinear (coordinateMap s p) (coordinateMap s q) (coordinateMap s r)) (x : F) :
    ringAutOfCoordinateCollinearity s h0 h1 hcol x=s x := rfl

end SymmetricSubgroupAsymptotics.CFSGAffinePlaneFieldReconstruction
