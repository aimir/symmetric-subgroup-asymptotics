import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group

/-! An involution cannot act fixed-point-freely on a nontrivial finite
2-group. Consequently disjoint positive conjugates in an actual fixed
subgroup remain disjoint before taking fixed points, provided the full
positive subgroup is a 2-group preserved by the involution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInvolutiveTwoGroupFixedIntersection
variable {G : Type*} [Group G]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem eq_one_of_involutive_fixed_free [Finite G] (hG : IsPGroup 2 G)
    (f : G→*G) (hinv : Function.Involutive f)
    (hfixed : ∀x,f x=x→x=1) (x : G) : x=1 := by
  have hodd : Odd (Nat.card G) :=
    MonoidHom.FixedPointFree.odd_card_of_involutive hfixed hinv
  obtain ⟨n,hn⟩ := hG.exists_card_eq
  have hn0 : n=0 := by
    by_contra hne
    exact hodd.not_two_dvd_nat (hn.symm ▸ dvd_pow_self 2 hne)
  have hcard : Nat.card G=1 := by rw [hn,hn0,pow_zero]
  letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact Subsingleton.elim x 1

theorem subgroup_eq_bot_of_fixed_trivial (Q : Subgroup G) [Finite Q]
    (hQ : IsPGroup 2 Q) (tau : G→*G) (hinv : Function.Involutive tau)
    (hstable : ∀x,x∈Q→tau x∈Q)
    (hfixed : ∀x,x∈Q→tau x=x→x=1) : Q=⊥ := by
  let f : Q→*Q :=
    { toFun := fun x=>⟨tau x.val,hstable x.val x.property⟩
      map_one' := Subtype.ext (map_one tau)
      map_mul' := fun x y=>Subtype.ext (map_mul tau x.val y.val) }
  have hf : Function.Involutive f := fun x=>Subtype.ext (hinv x.val)
  have hff : ∀x : Q,f x=x→x=1 := by
    intro x hx
    apply Subtype.ext
    exact hfixed x.val x.property (congrArg (fun y : Q=>y.val) hx)
  apply eq_bot_iff.mpr
  intro x hx
  exact Subgroup.mem_bot.mpr (congrArg (fun y : Q=>y.val)
    (eq_one_of_involutive_fixed_free hQ f hf hff ⟨x,hx⟩))

theorem inf_conjugate_eq_bot_of_fixed [Finite G]
    (P F : Subgroup G) (hP : IsPGroup 2 P) (tau : G→*G)
    (hinv : Function.Involutive tau) (hstable : ∀x,x∈P→tau x∈P)
    (hF : ∀x,x∈F↔tau x=x) (w : F)
    (hdisj : P.comap F.subtype⊓(P.comap F.subtype).map
      (MulAut.conj w).toMonoidHom=⊥) :
    P⊓P.map (MulAut.conj w.val).toMonoidHom=⊥ := by
  have hw : tau w.val=w.val := (hF w.val).mp w.property
  apply subgroup_eq_bot_of_fixed_trivial _ hP.to_inf_left tau hinv
  · intro x hx
    refine ⟨hstable x hx.1,?_⟩
    obtain ⟨a,ha,he⟩ := hx.2
    refine ⟨tau a,hstable a ha,?_⟩
    change w.val*tau a*w.val⁻¹=tau x
    rw [←he]
    change w.val*tau a*w.val⁻¹=tau (w.val*a*w.val⁻¹)
    rw [map_mul,map_mul,map_inv,hw]
  · intro x hx hxf
    let X : F := ⟨x,(hF x).mpr hxf⟩
    obtain ⟨a,ha,he⟩ := hx.2
    have haeq : a=w.val⁻¹*x*w.val := by
      change w.val*a*w.val⁻¹=x at he
      calc
        a=w.val⁻¹*(w.val*a*w.val⁻¹)*w.val := by group
        _=w.val⁻¹*x*w.val := by rw [he]
    have haf : tau a=a := by
      rw [haeq,map_mul,map_mul,map_inv,hw,hxf]
    let A : F := ⟨a,(hF a).mpr haf⟩
    have hboth : X∈P.comap F.subtype⊓(P.comap F.subtype).map
        (MulAut.conj w).toMonoidHom := by
      refine ⟨hx.1,A,ha,?_⟩
      apply Subtype.ext
      exact he
    rw [hdisj,Subgroup.mem_bot] at hboth
    exact congrArg (fun y : F=>y.val) hboth

end SymmetricSubgroupAsymptotics.CFSGInvolutiveTwoGroupFixedIntersection
