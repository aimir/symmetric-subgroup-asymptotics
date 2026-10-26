import SymmetricSubgroupAsymptotics.TernaryTwentySevenParabolicSubgroupClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound

/-! The actual primitive affine degree27 profile supplies its elementary
translation module. Its prime is derived from the literal regular group
cardinal; the same semidirect equivalence transports every original
subgroup into the ternary27 parabolic backend. Primitivity is explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineTernaryTwentySevenClassBound

local instance finiteSemidirect {N G : Type} [Group N] [Group G] [Finite N] [Finite G]
    (φ : G →* MulAut N) : Finite (N ⋊[φ] G) :=
  Finite.of_equiv (N×G) SemidirectProduct.equivProd.symm

private theorem subgroup_bound_prime_three
    {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]
    (hp : p=3) (hN : Nat.card N=27)
    (φ : G →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] G)) : Nat.card (ConjClasses L)≤12247 := by
  subst p
  exact TernaryTwentySevenParabolicSubgroupClassBound.subgroup_class_card_le_twelveTwoFortySeven
    hN φ hφ L

variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)
include P

theorem subgroup_class_card_le_twelveTwoFortySeven
    (hprimitive : MulAction.IsPreprimitive G X) (x : X)
    (hdegree : Nat.card X=27) (H : Subgroup G) : Nat.card (ConjClasses H)≤12247 := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hpdiv : P.p∣(3:ℕ)^3 := by
    have hh := P.V_pgroup.card_eq_or_dvd
    rw [P.card_eq x,hdegree] at hh
    simpa only [show (3:ℕ)^3=27 by decide] using hh.resolve_left (by decide : (27:ℕ)≠1)
  have hp : P.p=3 := Nat.prime_eq_prime_of_dvd_pow (m:=3) P.p_prime Nat.prime_three hpdiv
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  letI : CommGroup P.V := inferInstance
  let C := P.elementaryChart hprimitive
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  let a : Additive P.V ≃+ C.V := C.equiv.toAdditive
  letI : Module (ZMod P.p) (Additive P.V) := a.module (ZMod P.p)
  let e := P.semidirectEquiv x
  let L := H.map e.symm.toMonoidHom
  letI : Finite L := Finite.of_injective (fun z : L => z.val) Subtype.val_injective
  let b := e.symm.subgroupMap H
  have hc : Nat.card (ConjClasses H)≤Nat.card (ConjClasses L) :=
    Nat.card_le_card_of_surjective (ConjClasses.map b.symm.toMonoidHom)
      (ConjClasses.map_surjective b.symm.surjective)
  exact hc.trans (subgroup_bound_prime_three hp ((P.card_eq x).trans hdegree)
    (P.complementAction x) (P.complementAction_injective x) L)

end SymmetricSubgroupAsymptotics.PrimitiveAffineTernaryTwentySevenClassBound
