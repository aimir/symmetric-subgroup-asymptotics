import SymmetricSubgroupAsymptotics.BinaryFiveElementSemidirectClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleDerivedTarget
import Mathlib.Algebra.Module.TransferInstance

/-! The actual elementary translation module of a faithful primitive
degree32 affine profile discharges the binary five-space hypotheses.
Every original subgroup satisfies GM. Primitivity is essential here;
no claim is made about arbitrary nonprimitive order32 regular groups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThirtyTwoClassBound

local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : B →* MulAut A) : Finite (A ⋊[φ] B) :=
  Finite.of_equiv (A×B) SemidirectProduct.equivProd.symm

variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Nontrivial X]
    (P : PrimitiveAffineProfile G X)

include P in
theorem profile_prime_eq_two (x : X) (hdegree : Nat.card X=32) : P.p=2 := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hV : Nat.card P.V=32 := (P.card_eq x).trans hdegree
  letI : Nontrivial P.V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨n, hnpos, hn⟩ := P.V_pgroup.nontrivial_iff_card.mp inferInstance
  have hpdiv : P.p ∣ (2 : ℕ)^5 := by
    rw [show (2 : ℕ)^5=32 by decide, ←hV, hn]
    exact dvd_pow_self P.p hnpos.ne'
  have hp2 : P.p ∣ 2 := P.p_prime.dvd_of_dvd_pow hpdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
  · exact False.elim (P.p_prime.ne_one h)
  · exact h

include P in
theorem subgroup_class_card_le
    (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hdegree : Nat.card X=32) (H : Subgroup G) :
    Nat.card (ConjClasses H) ≤ 16252976 := by
  have hp := profile_prime_eq_two P x hdegree
  have hV : Nat.card P.V=32 := (P.card_eq x).trans hdegree
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
  letI : Finite (ConjClasses L) :=
    Finite.of_surjective (@ConjClasses.mk L _) ConjClasses.mk_surjective
  let b := e.symm.subgroupMap H
  have hc : Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses L) :=
    Nat.card_le_card_of_surjective (ConjClasses.map b.symm.toMonoidHom)
      (ConjClasses.map_surjective b.symm.surjective)
  exact hc.trans (BinaryFiveElementSemidirectClassBound.subgroup_class_card_le
    hp hV (P.complementAction x) (P.complementAction_injective x) L)

include P in
theorem subgroup_class_cube_le_garonziMaroti
    (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hdegree : Nat.card X=32) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  calc
    Nat.card (ConjClasses H)^3 ≤ 16252976^3 :=
      Nat.pow_le_pow_left (subgroup_class_card_le P hprimitive x hdegree H) 3
    _ ≤ 5^(Nat.card X-1) := by rw [hdegree]; decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThirtyTwoClassBound
