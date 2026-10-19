import Mathlib.RepresentationTheory.Irreducible
import SymmetricSubgroupAsymptotics.RepresentationSemisimpleSurjectiveInflation
import Mathlib.RingTheory.SimpleModule.Basic

/-! Semisimple restriction turns an actual subquotient into an injected
module for the normal subgroup. A normal kernel would then supply fixed
vectors in the original envelope. This lemma contains no wreath or
capacity conclusion among its assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

 theorem faithful_normal_restriction_of_semisimple_subquotient
    {k G V A W : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    [AddCommGroup A] [Module k A]
    [AddCommGroup W] [Module k W] [Nontrivial W]
    (K : Subgroup G) [K.Normal]
    (rho : Representation k G V) (sigma : Representation k G A)
    (tau : Representation k G W)
    [IsSemisimpleModule k[K] (Representation.asModule (rho.comp K.subtype))]
    (j : sigma.IntertwiningMap rho) (hj : Function.Injective j)
    (q : sigma.IntertwiningMap tau) (hq : Function.Surjective q)
    (hfixed : ∀ (L : Subgroup G) [L.Normal],L≤K → L≠⊥ →
      ∀ v : V,(∀ l : L,rho l.val v=v) → v=0) :
    Function.Injective (tau.comp K.subtype) := by
  let rhoK : Representation k K V := rho.comp K.subtype
  let sigmaK : Representation k K A := sigma.comp K.subtype
  let tauK : Representation k K W := tau.comp K.subtype
  let jK : sigmaK.IntertwiningMap rhoK :=
    { toLinearMap := j.toLinearMap
      isIntertwining' g := j.isIntertwining' g.val }
  let qK : sigmaK.IntertwiningMap tauK :=
    { toLinearMap := q.toLinearMap
      isIntertwining' g := q.isIntertwining' g.val }
  let jm : sigmaK.asModule →ₗ[k[K]] rhoK.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ jK
  letI : IsSemisimpleModule k[K] sigmaK.asModule :=
    IsSemisimpleModule.of_injective jm hj
  let qm : sigmaK.asModule →ₗ[k[K]] tauK.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ qK
  obtain ⟨sm,hsm⟩ := IsSemisimpleModule.lifting_property qm hq
    (LinearMap.id : tauK.asModule →ₗ[k[K]] tauK.asModule)
  let s : tauK.IntertwiningMap sigmaK :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm sm
  have hs : Function.Injective s := by
    intro x y he
    have hx : qK (s x)=x := LinearMap.congr_fun hsm x
    have hy : qK (s y)=y := LinearMap.congr_fun hsm y
    exact hx.symm.trans ((congrArg qK he).trans hy)
  let emb : tauK.IntertwiningMap rhoK := jK.comp s
  have hemb : Function.Injective emb := hj.comp hs
  let L : Subgroup G := K ⊓ tau.asGroupHom.ker
  letI : L.Normal := inferInstanceAs (K ⊓ tau.asGroupHom.ker).Normal
  have hLK : L≤K := inf_le_left
  have hL : L=⊥ := by
    by_contra hn
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    have hv : emb w=0 := hfixed L hLK hn (emb w) (by
      intro l
      have ht : tau l.val=1 := congrArg Units.val l.property.2
      have hh := Representation.IntertwiningMap.isIntertwining _ _ emb
        (⟨l.val,hLK l.property⟩ : K) w
      change emb (tau l.val w)=rho l.val (emb w) at hh
      rw [ht,Module.End.one_apply] at hh
      exact hh.symm)
    exact hw (hemb (hv.trans emb.map_zero.symm))
  have hu : Function.Injective (tau.asGroupHom.comp K.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxL : x.val∈L := ⟨x.property,hx⟩
    rw [hL,Subgroup.mem_bot] at hxL
    exact Subgroup.mem_bot.mpr (Subtype.ext hxL)
  intro x y hxy
  apply hu
  apply Units.ext
  exact hxy

end SymmetricSubgroupAsymptotics
