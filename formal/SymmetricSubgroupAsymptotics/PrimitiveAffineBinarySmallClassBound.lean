import SymmetricSubgroupAsymptotics.BinarySmallElementSemidirectClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleDerivedTarget
import Mathlib.Algebra.Module.TransferInstance

/-! Genuine primitive affine profiles of degrees8 and16 satisfy GM
for every original subgroup. The actual elementary translation chart,
faithful complement action and literal semidirect equivalence discharge
all linear and counting inputs; there is no finite-group census. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound

local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : B →* MulAut A) : Finite (A ⋊[φ] B) :=
  Finite.of_equiv (A×B) SemidirectProduct.equivProd.symm

variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Nontrivial X]
    (P : PrimitiveAffineProfile G X)

include P in
theorem profile_prime_eq_two_of_degree_pow (x : X) (a : ℕ)
    (hdegree : Nat.card X=2^a) : P.p=2 := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : Nontrivial P.V := (P.pointEquiv x).symm.injective.nontrivial
  have hV : Nat.card P.V=2^a := (P.card_eq x).trans hdegree
  obtain ⟨n,hnpos,hn⟩ := P.V_pgroup.nontrivial_iff_card.mp inferInstance
  have hpdiv : P.p ∣ (2 : ℕ)^a := by
    rw [←hV,hn]
    exact dvd_pow_self P.p hnpos.ne'
  have hp2 : P.p ∣ 2 := P.p_prime.dvd_of_dvd_pow hpdiv
  rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
  · exact False.elim (P.p_prime.ne_one h)
  · exact h

include P in
theorem subgroup_class_card_bound (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hdegree : Nat.card X=8 ∨ Nat.card X=16) (H : Subgroup G) :
    (Nat.card X=8 ∧ Nat.card (ConjClasses H) ≤ 36) ∨
      (Nat.card X=16 ∧ Nat.card (ConjClasses H) ≤ 2312) := by
  have hp : P.p=2 := by
    rcases hdegree with h8 | h16
    · exact profile_prime_eq_two_of_degree_pow P x 3 (by simpa using h8)
    · exact profile_prime_eq_two_of_degree_pow P x 4 (by simpa using h16)
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
  rcases hdegree with h8 | h16
  · left
    refine ⟨h8,hc.trans ?_⟩
    have hV : Nat.card P.V=8 := (P.card_eq x).trans h8
    exact BinarySmallElementSemidirectClassBound.subgroup_class_card_le_thirtySix
      hp hV (P.complementAction x) (P.complementAction_injective x) L
  · right
    refine ⟨h16,hc.trans ?_⟩
    have hV : Nat.card P.V=16 := (P.card_eq x).trans h16
    exact BinarySmallElementSemidirectClassBound.subgroup_class_card_le_twoThousandThreeTwelve
      hp hV (P.complementAction x) (P.complementAction_injective x) L

include P in
theorem subgroup_class_cube_le_garonziMaroti
    (hprimitive : MulAction.IsPreprimitive G X) (x : X)
    (hdegree : Nat.card X=8 ∨ Nat.card X=16) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases subgroup_class_card_bound P hprimitive x hdegree H with ⟨hn,hc⟩ | ⟨hn,hc⟩
  · calc
      Nat.card (ConjClasses H)^3 ≤ 36^3 := Nat.pow_le_pow_left hc 3
      _ ≤ 5^(Nat.card X-1) := by rw [hn]; decide +kernel
  · calc
      Nat.card (ConjClasses H)^3 ≤ 2312^3 := Nat.pow_le_pow_left hc 3
      _ ≤ 5^(Nat.card X-1) := by rw [hn]; decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound
