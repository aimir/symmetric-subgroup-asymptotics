import SymmetricSubgroupAsymptotics.AffinePrimePowerOrderBound
import SymmetricSubgroupAsymptotics.AffinePrimePowerClassNumerics
import Mathlib.GroupTheory.GroupAction.CardCommute

/-! Infinite actual affine families, with EVERY correlated subgroup:
degree p squared for p>=5, and degree p cubed for p>=3. No elementary
abelian or primitive action hypothesis is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffinePrimePowerSubgroupClassBound
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_square_degree_cube_le (x : X) (hp : 5 ≤ P.p)
    (hdegree : Nat.card X=P.p^2) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hc : Nat.card (ConjClasses H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hs : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective H.subtype Subtype.val_injective
  have ho := AffinePrimePowerOrderBound.card_le_degree_mul_prime_log_power P x
  rw [hdegree,Nat.log_pow P.p_prime.one_lt] at ho
  have hbound : Nat.card (ConjClasses H) ≤ P.p^6 := by
    calc
      Nat.card (ConjClasses H) ≤ P.p^2*(P.p^2)^2 := (hc.trans hs).trans ho
      _ = P.p^6 := by ring
  rw [hdegree]
  have h := Nat.pow_le_pow_left hbound 3
  rw [← pow_mul] at h
  exact h.trans (AffinePrimePowerClassNumerics.square_degree_budget P.p hp)

include P in
theorem subgroup_cube_degree_cube_le (x : X) (hp : 3 ≤ P.p)
    (hdegree : Nat.card X=P.p^3) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hc : Nat.card (ConjClasses H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hs : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective H.subtype Subtype.val_injective
  have ho := AffinePrimePowerOrderBound.card_le_degree_mul_prime_log_power P x
  rw [hdegree,Nat.log_pow P.p_prime.one_lt] at ho
  have hbound : Nat.card (ConjClasses H) ≤ P.p^12 := by
    calc
      Nat.card (ConjClasses H) ≤ P.p^3*(P.p^3)^3 := (hc.trans hs).trans ho
      _ = P.p^12 := by ring
  rw [hdegree]
  have h := Nat.pow_le_pow_left hbound 3
  rw [← pow_mul] at h
  exact h.trans (AffinePrimePowerClassNumerics.cube_degree_budget P.p hp)

end SymmetricSubgroupAsymptotics.AffinePrimePowerSubgroupClassBound
