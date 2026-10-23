import SymmetricSubgroupAsymptotics.CFSGCosetDataIndex
import Mathlib.Algebra.Ring.Aut
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group

/-! Count a faithful action on two families of field parameters modulo
an actually realized compatible scalar group. Compatible automorphisms
of a subfield are determined by their action on the larger field, so
the field factor is the automorphism count of that larger field alone. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoFieldSemilinearCosetIndex
open CFSGCosetDataIndex

variable {K F : Type*} [Field K] [Field F]

def compatibleFields (iota : F→+*K) :=
  {p : RingAut K × RingAut F // ∀x,p.1 (iota x)=iota (p.2 x)}

theorem compatibleFields_fst_injective (iota : F→+*K) :
    Function.Injective (fun p : compatibleFields iota => p.val.1) := by
  intro p q he
  apply Subtype.ext
  apply Prod.ext he
  apply RingEquiv.ext
  intro x
  apply iota.injective
  exact (p.property x).symm.trans ((DFunLike.congr_fun he (iota x)).trans (q.property x))

theorem compatibleFields_card_le (iota : F→+*K) [Finite K] :
    Nat.card (compatibleFields iota)≤Nat.card (RingAut K) := by
  letI : Finite (RingAut K) := Finite.of_injective
    (fun s : RingAut K => (s : K→K)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective _ (compatibleFields_fst_injective iota)

variable [Finite K] {G A B D I J : Type*}
    [Group G] [Group A] [Group B] [CommGroup D] [Finite D]

theorem scalar_lift_index_le (iota : F→+*K)
    (u : I→K→G) (v : J→F→G) (rho : A→*MulAut G)
    (hfaith : ∀a b : A,(∀i x,rho a (u i x)=rho b (u i x))→
      (∀j y,rho a (v j y)=rho b (v j y))→a=b)
    (pairScale : D→*(I→Kˣ)) (singleScale : D→*(J→Fˣ))
    (hsem : ∀a : A,∃(s : compatibleFields iota) (c : D),
      (∀i x,rho a (u i x)=u i ((pairScale c i : K)*s.val.1 x)) ∧
      (∀j y,rho a (v j y)=v j ((singleScale c j : F)*s.val.2 y)))
    (lift : B→*A) (chi : B→*D)
    (hpair : ∀t i x,rho (lift t) (u i x)=u i ((pairScale (chi t) i : K)*x))
    (hsingle : ∀t j y,rho (lift t) (v j y)=v j ((singleScale (chi t) j : F)*y)) :
    lift.range.index≤chi.range.index*Nat.card (RingAut K) := by
  classical
  letI : Finite (RingAut K) := Finite.of_injective
    (fun s : RingAut K => (s : K→K)) DFunLike.coe_injective
  letI : Finite (compatibleFields iota) :=
    Finite.of_injective _ (compatibleFields_fst_injective iota)
  choose s c hs using hsem
  have hindex : lift.range.index≤chi.range.index*Nat.card (compatibleFields iota) := by
    apply index_le_of_coset_data lift.range chi.range c s
    intro a b hc he
    obtain ⟨t,ht⟩ := QuotientGroup.eq.mp hc
    have hscale : chi t*c a=c b := by
      rw [ht]
      calc
        (c a)⁻¹*c b*c a=((c a)⁻¹*c a)*c b := by ac_rfl
        _=c b := by rw [inv_mul_cancel,one_mul]
    have hpk (i : I) : (pairScale (chi t) i : K)*(pairScale (c a) i : K)=
        (pairScale (c b) i : K) := by
      have hh : pairScale (chi t)*pairScale (c a)=pairScale (c b) := by
        rw [←map_mul,hscale]
      exact congrArg Units.val (congrFun hh i)
    have hsf (j : J) : (singleScale (chi t) j : F)*(singleScale (c a) j : F)=
        (singleScale (c b) j : F) := by
      have hh : singleScale (chi t)*singleScale (c a)=singleScale (c b) := by
        rw [←map_mul,hscale]
      exact congrArg Units.val (congrFun hh j)
    have hb : lift t*a=b := by
      apply hfaith
      · intro i x
        calc
          rho (lift t*a) (u i x)=rho (lift t) (rho a (u i x)) := by rw [map_mul]; rfl
          _=rho (lift t) (u i ((pairScale (c a) i : K)*(s a).val.1 x)) :=
            congrArg (rho (lift t)) ((hs a).1 i x)
          _=u i ((pairScale (chi t) i : K)*((pairScale (c a) i : K)*(s a).val.1 x)) := hpair t i _
          _=u i ((pairScale (c b) i : K)*(s b).val.1 x) := by rw [←mul_assoc,hpk,he]
          _=rho b (u i x) := ((hs b).1 i x).symm
      · intro j y
        calc
          rho (lift t*a) (v j y)=rho (lift t) (rho a (v j y)) := by rw [map_mul]; rfl
          _=rho (lift t) (v j ((singleScale (c a) j : F)*(s a).val.2 y)) :=
            congrArg (rho (lift t)) ((hs a).2 j y)
          _=v j ((singleScale (chi t) j : F)*((singleScale (c a) j : F)*(s a).val.2 y)) := hsingle t j _
          _=v j ((singleScale (c b) j : F)*(s b).val.2 y) := by rw [←mul_assoc,hsf,he]
          _=rho b (v j y) := ((hs b).2 j y).symm
    refine ⟨t⁻¹,?_⟩
    rw [map_inv,←hb]
    group
  exact hindex.trans (Nat.mul_le_mul_left _ (compatibleFields_card_le iota))

end SymmetricSubgroupAsymptotics.CFSGTwoFieldSemilinearCosetIndex
