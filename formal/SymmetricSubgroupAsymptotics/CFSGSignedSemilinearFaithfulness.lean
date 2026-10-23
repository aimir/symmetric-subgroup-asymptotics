import SymmetricSubgroupAsymptotics.CFSGSemilinearRootCosetIndex

/-! Reciprocal signed semilinear data make the positive parameters
faithful whenever all signed parameters are faithful. This is a generic
counting bridge; the later actual model must prove its common-field and
signed-generation inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGSignedSemilinearFaithfulness
variable {K G A I : Type*} [Field K] [Group G] [Group A]

 theorem positive_faithful_of_signed_semilinear
    (u : Bool→I→K→G) (rho : A→*MulAut G) (i0 : I)
    (hinj : ∀i,Function.Injective (u false i))
    (hfaith : ∀f g : A,(∀neg i x,rho f (u neg i x)=rho g (u neg i x))→f=g)
    (hsemi : ∀f : A,∃(c : I→Kˣ)(tau : K≃+*K),∀neg i x,
      rho f (u neg i x)=u neg i
        (((if neg then (c i)⁻¹ else c i : Kˣ) : K)*tau x)) :
    ∀f g : A,(∀i x,rho f (u false i x)=rho g (u false i x))→f=g := by
  intro f g hpos
  obtain ⟨cf,tauf,hf⟩ := hsemi f
  obtain ⟨cg,taug,hg⟩ := hsemi g
  have hc (i : I) : cf i=cg i := by
    apply Units.val_injective
    have he := hinj i ((hf false i 1).symm.trans ((hpos i 1).trans (hg false i 1)))
    simpa only [Bool.false_eq_true,if_false,map_one,mul_one] using he
  have htau : tauf=taug := by
    ext x
    have he := hinj i0 ((hf false i0 x).symm.trans ((hpos i0 x).trans (hg false i0 x)))
    have hex : (cf i0 : K)*tauf x=(cg i0 : K)*taug x := by
      simpa only [Bool.false_eq_true,if_false] using he
    rw [hc i0] at hex
    exact mul_left_cancel₀ (Units.ne_zero (cg i0)) hex
  apply hfaith f g
  intro neg i x
  rw [hf,hg,htau,hc i]

end SymmetricSubgroupAsymptotics.CFSGSignedSemilinearFaithfulness
