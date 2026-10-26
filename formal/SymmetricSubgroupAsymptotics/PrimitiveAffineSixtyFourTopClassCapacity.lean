import SymmetricSubgroupAsymptotics.BinarySixtyFourElementSemidirectClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound

/-! Same-profile transport and actual unsigned small-fibre arithmetic
for primitive affine tops on64 points. The explicit preprimitive premise
supplies the elementary module; a bare regular p-group is not enough. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixtyFourTopClassCapacity
open BinarySixtyFourElementSemidirectClassBound (classBudget)

local instance finiteSemidirect {N G : Type} [Group N] [Group G] [Finite N] [Finite G]
    (φ : G →* MulAut N) : Finite (N ⋊[φ] G) :=
  Finite.of_equiv (N × G) SemidirectProduct.equivProd.symm

variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_card_le (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hdegree : Nat.card X=64) (H : Subgroup G) :
    Nat.card (ConjClasses H) ≤ classBudget := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hp : P.p=2 := PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow
    P x 6 (by simpa using hdegree)
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
  letI : Finite (ConjClasses L) := Finite.of_surjective
    (@ConjClasses.mk L _) ConjClasses.mk_surjective
  let b := e.symm.subgroupMap H
  have hc : Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses L) :=
    Nat.card_le_card_of_surjective (ConjClasses.map b.symm.toMonoidHom)
      (ConjClasses.map_surjective b.symm.surjective)
  have hV : Nat.card P.V=64 := (P.card_eq x).trans hdegree
  exact hc.trans (BinarySixtyFourElementSemidirectClassBound.subgroup_class_card_le
    hp hV (P.complementAction x) (P.complementAction_injective x) L)

theorem budget_ge_eleven : 11 ≤ classBudget := by unfold classBudget; decide

theorem binary_unsigned_capacity : ((classBudget+1)*2^(64-2))^3 ≤ 5^(2*64-1) := by
  unfold classBudget
  decide +kernel

theorem ternary_capacity : (3^64*classBudget)^3 ≤ 5^(3*64-1) := by
  unfold classBudget
  decide +kernel

theorem affine_order_lt_factorial : 64*64^Nat.log 2 64 < (64:ℕ).factorial := by
  decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixtyFourTopClassCapacity
