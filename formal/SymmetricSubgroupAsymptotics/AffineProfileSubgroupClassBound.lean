import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.AffineClassOrderNumerics
import Mathlib.GroupTheory.GroupAction.CardCommute

/-! Every subgroup of an actual faithful affine profile satisfies the GM
cube in the ambient degree from64 onward. No primitive-group order theorem,
finite catalogue correspondence, class estimate, or CFSG input is assumed.
In particular this bounds every subnormal component subgroup in that range. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffineProfileSubgroupClassBound

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_cube_le_garonziMaroti (x : X)
    (hn : 64 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hc : Nat.card (ConjClasses H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hsub : Nat.card H ≤ Nat.card G :=
    Nat.card_le_card_of_injective H.subtype Subtype.val_injective
  have horder := P.card_le_domain_pow_log x
  exact (Nat.pow_le_pow_left ((hc.trans hsub).trans horder) 3).trans
    (AffineClassOrderNumerics.domain_pow_log_cube_le (Nat.card X) hn)

include P in
theorem class_cube_le_garonziMaroti (x : X) (hn : 64 ≤ Nat.card X) :
    Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1) := by
  have hc : Nat.card (ConjClasses G) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  exact (Nat.pow_le_pow_left (hc.trans (P.card_le_domain_pow_log x)) 3).trans
    (AffineClassOrderNumerics.domain_pow_log_cube_le (Nat.card X) hn)

end SymmetricSubgroupAsymptotics.AffineProfileSubgroupClassBound
