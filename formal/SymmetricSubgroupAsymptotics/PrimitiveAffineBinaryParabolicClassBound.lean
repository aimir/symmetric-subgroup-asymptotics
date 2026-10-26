import SymmetricSubgroupAsymptotics.BinaryThirtyTwoParabolicSubgroupClassBound
import SymmetricSubgroupAsymptotics.BinaryEightElementSemidirectClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound

/-! Actual primitive affine profiles on8/16/32 points supply the SAME
elementary translation chart required by the parabolic recursion. The
preprimitive premise is explicit; a bare regular p-subgroup is not
silently treated as an elementary module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryParabolicClassBound

def classBudget (n : ℕ) : ℕ := if n=8 then 24 else if n=16 then 772 else 351240

local instance finiteSemidirect {N G : Type} [Group N] [Group G] [Finite N] [Finite G]
    (φ : G →* MulAut N) : Finite (N ⋊[φ] G) :=
  Finite.of_equiv (N × G) SemidirectProduct.equivProd.symm

variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_card_le
    (hprimitive : MulAction.IsPreprimitive G X) (x : X)
    (hdegree : Nat.card X=8 ∨ Nat.card X=16 ∨ Nat.card X=32) (H : Subgroup G) :
    Nat.card (ConjClasses H) ≤ classBudget (Nat.card X) := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp
    (by rcases hdegree with h|h|h <;> omega)
  have hp : P.p=2 := by
    rcases hdegree with h|h|h
    · exact PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow
        P x 3 (by simpa using h)
    · exact PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow
        P x 4 (by simpa using h)
    · exact PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow
        P x 5 (by simpa using h)
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
  rcases hdegree with h8|h16|h32
  · have hV : Nat.card P.V=8 := (P.card_eq x).trans h8
    have hb := hc.trans
      (BinaryEightElementSemidirectClassBound.subgroup_class_card_le_twentyFour
        hp hV (P.complementAction x) (P.complementAction_injective x) L)
    simpa only [classBudget,h8,if_pos rfl] using hb
  · have hV : Nat.card P.V=16 := (P.card_eq x).trans h16
    have hb := hc.trans
      (BinarySixteenParabolicSubgroupClassBound.subgroup_class_card_le_sevenSeventyTwo
        hp hV (P.complementAction x) (P.complementAction_injective x) L)
    simpa only [classBudget,h16,if_neg (by decide : (16:ℕ)≠8),if_pos rfl] using hb
  · have hV : Nat.card P.V=32 := (P.card_eq x).trans h32
    have hb := hc.trans
      (BinaryThirtyTwoParabolicSubgroupClassBound.subgroup_class_card_le_threeFiftyOneTwoForty
        hp hV (P.complementAction x) (P.complementAction_injective x) L)
    simpa only [classBudget,h32,if_neg (by decide : (32:ℕ)≠8),
      if_neg (by decide : (32:ℕ)≠16)] using hb

end SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryParabolicClassBound
