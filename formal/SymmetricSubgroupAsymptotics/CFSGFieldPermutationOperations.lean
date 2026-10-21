import SymmetricSubgroupAsymptotics.CFSGAffinePlaneFieldReconstruction

/-! The two field identities supplied by the original incidence
configurations already force an actual field automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFieldPermutationOperations
variable {F : Type*} [Field F]

private theorem map_neg_one (s : F≃F) (h1 : s 1=1)
    (hmul : ∀a b,s (a*b)=s a*s b) : s (-1)=-1 := by
  have hs : s (-1)*s (-1)=1 := by rw [←hmul,neg_one_mul,neg_neg,h1]
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

theorem map_add (s : F≃F) (h0 : s 0=0) (h1 : s 1=1)
    (hmul : ∀a b,s (a*b)=s a*s b) (hcomp : ∀a,s (1-a)=1-s a)
    (x y : F) : s (x+y)=s x+s y := by
  let h : F→*₀F := { toFun := s, map_zero' := h0, map_one' := h1, map_mul' := hmul }
  have hneg (a : F) : s (-a)=-s a := by
    rw [show -a=(-1)*a by ring,hmul,map_neg_one s h1 hmul,neg_one_mul]
  have hsub (a b : F) : s (a-b)=s a-s b := by
    by_cases ha : a=0
    · subst a
      simp only [zero_sub,hneg,h0]
    · have hsa : s a≠0 := fun he => ha (s.injective (he.trans h0.symm))
      have he : a-b=a*(1-b/a) := by field_simp [ha]
      rw [he,hmul,hcomp]
      have hdiv : s (b/a)=s b/s a := map_div₀ h b a
      rw [hdiv]
      field_simp [hsa]
      <;> ring
  rw [show x+y=x-(-y) by ring,hsub,hneg,sub_neg_eq_add]

def ringAutOfOperations (s : F≃F) (h0 : s 0=0) (h1 : s 1=1)
    (hmul : ∀a b,s (a*b)=s a*s b) (hcomp : ∀a,s (1-a)=1-s a) : F≃+*F :=
  { s with map_mul' := hmul, map_add' := map_add s h0 h1 hmul hcomp }

@[simp] theorem ringAutOfOperations_apply (s : F≃F) (h0 : s 0=0) (h1 : s 1=1)
    (hmul : ∀a b,s (a*b)=s a*s b) (hcomp : ∀a,s (1-a)=1-s a) (x : F) :
    ringAutOfOperations s h0 h1 hmul hcomp x=s x := rfl

end SymmetricSubgroupAsymptotics.CFSGFieldPermutationOperations
