import SymmetricSubgroupAsymptotics.BinaryEightElementSemidirectClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound

/-! The exact degree-eight affine profile transfers the stronger actual
semidirect subgroup bound24 through its original elementary translation
chart. The resulting cube gains two powers of5 relative to the degree,
as required for the two/three-block original-action installer. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.AffineDegreeEightSubgroupClassGap

local instance finiteSemidirect {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : B →* MulAut A) : Finite (A ⋊[φ] B) :=
  Finite.of_equiv (A×B) SemidirectProduct.equivProd.symm

variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Nontrivial X]
    (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_card_le_twentyFour
    (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hdegree : Nat.card X=8) (H : Subgroup G) :
    Nat.card (ConjClasses H) ≤ 24 := by
  have hp : P.p=2 :=
    PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow
      P x 3 (by simpa using hdegree)
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
  have hV : Nat.card P.V=8 := (P.card_eq x).trans hdegree
  exact hc.trans (BinaryEightElementSemidirectClassBound.subgroup_class_card_le_twentyFour
    hp hV (P.complementAction x) (P.complementAction_injective x) L)

include P in
theorem subgroup_class_cube_gap
    (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hdegree : Nat.card X=8) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  calc
    Nat.card (ConjClasses H)^3 ≤ 24^3 :=
      Nat.pow_le_pow_left (subgroup_class_card_le_twentyFour P hprimitive x hdegree H) 3
    _ ≤ 5^(Nat.card X-2) := by rw [hdegree]; decide +kernel

end SymmetricSubgroupAsymptotics.AffineDegreeEightSubgroupClassGap
