import SymmetricSubgroupAsymptotics.CFSGTwistedDOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexStarLower
import SymmetricSubgroupAsymptotics.CFSGTwistedDOuterCardinality

/-! Actual twisted-D component budgets for each literal proper index.
The fixed-field matrix order and proved outer reconstruction combine
before passing to index powers; rank four has a bounded exponent34. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDProperIndexOrderBudget
open CFSGTwistedDOriginalOrderUpper CFSGTwistedDRelativeProjectiveModel
open CFSGTwistedDIndexStarLower CFSGTwistedDOuterCardinality
open CFSGTwistedDRelativeElementaryGroup PrimitiveSocleRawStructure
open CFSGTwistedDProjectiveUnipotent

theorem component_power_le_index_log_power (q r m : ℕ) (hq : 2≤q) (hr : 5≤r)
    (hindex : q^(r-2)≤m) : q^(4*r^2+4)≤m^(4*Nat.log 2 m+23) := by
  have hqpos : 0<q := by omega
  have hm : 2≤m := hq.trans ((Nat.le_self_pow (by omega : r-2≠0) q).trans hindex)
  have hlog : r-2≤Nat.log 2 m := Nat.le_log_of_pow_le (by decide)
    ((Nat.pow_le_pow_left hq (r-2)).trans hindex)
  have hrank : r≤Nat.log 2 m+2 := by omega
  have hexp : 4*r^2+4≤(r-2)*(4*r+15) := by
    have hrs : r-2+2=r := by omega
    nlinarith
  calc
    q^(4*r^2+4)≤q^((r-2)*(4*r+15)) := Nat.pow_le_pow_right hqpos hexp
    _ =(q^(r-2))^(4*r+15) := pow_mul q (r-2) (4*r+15)
    _ ≤m^(4*r+15) := Nat.pow_le_pow_left hindex _
    _ ≤m^(4*Nat.log 2 m+23) := Nat.pow_le_pow_right (by omega) (by omega)

theorem typeTwistedD_field_power_le_proper_index (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (H : Subgroup (CFSG.Models.TwistedD r q)) (hH : H≠⊤) : q.order^(r-2)≤H.index := by
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+4 := ⟨r-4,by omega⟩
  let e := originalRelativeProjectiveEquiv s q
  letI : IsSimpleGroup (Projective s q) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := projective_field_power_le_proper_index s q (H.map e.toMonoidHom) hmap
  have hidx : (H.map e.toMonoidHom).index=H.index := H.index_map_equiv e
  rw [hidx] at hi
  simpa only [show s+4-2=s+2 by omega] using hi

theorem typeTwistedD_outer_card_le_field_fourth (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q)) :
    Nat.card (Outer (CFSG.Models.TwistedD r q))≤q.order^4 := by
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hf : q.exponent≤q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hc : 8≤q.order^3 := (by decide : 8≤2^3).trans (Nat.pow_le_pow_left hq 3)
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+4 := ⟨r-4,by omega⟩
  calc
    Nat.card (Outer (CFSG.Models.TwistedD (s+4) q))≤8*q.exponent :=
      original_outer_card_le_eight_exponent s q hn
    _ ≤8*q.order := Nat.mul_le_mul_left _ hf
    _ ≤q.order^3*q.order := Nat.mul_le_mul_right _ hc
    _ =q.order^4 := (pow_succ q.order 3).symm

theorem typeTwistedD_order_mul_outer_le_field_power (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q)) :
    Nat.card (CFSG.Models.TwistedD r q)*Nat.card (Outer (CFSG.Models.TwistedD r q))≤
      q.order^(4*r^2+4) := by
  calc
    _ ≤q.order^(4*r^2)*q.order^4 := Nat.mul_le_mul
      (typeTwistedD_order_le_fixed_matrix_power r hr q)
      (typeTwistedD_outer_card_le_field_fourth r hr q hn)
    _ =q.order^(4*r^2+4) := (pow_add _ _ _).symm

theorem typeTwistedD_high_order_mul_outer_le_proper_index_log_power
    (r : ℕ) (hr : 5≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q))
    (H : Subgroup (CFSG.Models.TwistedD r q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.TwistedD r q)*Nat.card (Outer (CFSG.Models.TwistedD r q))≤
      H.index^(4*Nat.log 2 H.index+23) := by
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact (typeTwistedD_order_mul_outer_le_field_power r (by omega) q hn).trans
    (component_power_le_index_log_power q.order r H.index hq hr
      (typeTwistedD_field_power_le_proper_index r (by omega) q H hH))

theorem typeTwistedD_four_order_mul_outer_le_proper_index_power (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD 4 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD 4 q))
    (H : Subgroup (CFSG.Models.TwistedD 4 q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.TwistedD 4 q)*Nat.card (Outer (CFSG.Models.TwistedD 4 q))≤H.index^34 := by
  have hi : q.order^2≤H.index := typeTwistedD_field_power_le_proper_index 4 (by decide) q H hH
  calc
    _ ≤q.order^68 := typeTwistedD_order_mul_outer_le_field_power 4 (by decide) q hn
    _ =(q.order^2)^34 := by rw [←pow_mul]
    _ ≤H.index^34 := Nat.pow_le_pow_left hi 34

end SymmetricSubgroupAsymptotics.CFSGTwistedDProperIndexOrderBudget
