import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarLower
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters

/-! An order-plus-outer budget for EVERY proper subgroup of the
ORIGINAL type-D simple model. The inputs are the proved literal matrix
quotient, the actual q^(r-1) root star and the proved outer bounds. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDProperIndexOrderBudget
open CFSGOrthogonalDOriginalOrderUpper CFSGOrthogonalDSerreMatrices
open CFSGReduction PrimitiveSocleRawStructure

theorem matrix_power_le_index_log_power (q r m : ℕ) (hq : 2≤q) (hr : 4≤r)
    (hindex : q^(r-1)≤m) : q^(4*r^2)≤m^(4*Nat.log 2 m+10) := by
  have hqpos : 0<q := by omega
  have hm : 2≤m := hq.trans ((Nat.le_self_pow (by omega : r-1≠0) q).trans hindex)
  have hlog : r-1≤Nat.log 2 m := Nat.le_log_of_pow_le (by decide)
    ((Nat.pow_le_pow_left hq (r-1)).trans hindex)
  have hrank : r≤Nat.log 2 m+1 := by omega
  have hexp : 4*r^2≤(r-1)*(4*r+6) := by
    have hrs : r-1+1=r := by omega
    nlinarith
  have hlast : 4*r+6≤4*Nat.log 2 m+10 := by omega
  calc
    q^(4*r^2)≤q^((r-1)*(4*r+6)) := Nat.pow_le_pow_right hqpos hexp
    _ =(q^(r-1))^(4*r+6) := pow_mul q (r-1) (4*r+6)
    _ ≤m^(4*r+6) := Nat.pow_le_pow_left hindex _
    _ ≤m^(4*Nat.log 2 m+10) := Nat.pow_le_pow_right (by omega) hlast

theorem typeD_field_power_le_proper_index (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)]
    (H : Subgroup (CFSG.Models.D r q)) (hH : H≠⊤) : q.order^(r-1)≤H.index := by
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+4 := ⟨r-4,by omega⟩
  let e := serreProjectiveEquivElementaryProjective q.Field s
  letI : IsSimpleGroup (elementaryProjective q.Field (s+4)) := e.symm.isSimpleGroup
  have hmap : H.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := CFSGOrthogonalDIndexStarLower.projective_field_power_le_proper_index
    q.Field s (H.map e.toMonoidHom) hmap
  have hidx : (H.map e.toMonoidHom).index=H.index := H.index_map_equiv e
  rw [hidx] at hi
  simpa only [q.card_field,show s+4-1=s+3 by omega] using hi

theorem typeD_outer_card_le_twentyFour_exponent (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] :
    Nat.card (Outer (CFSG.Models.D r q))≤24*q.exponent := by
  have hb : Nat.card (Outer (CFSG.Models.D r q))≤24*Nat.card (q.Field≃+*q.Field) := by
    by_cases hfour : r=4
    · subst r
      exact typeD_four_outer_card_le q
    · exact (typeD_high_outer_card_le r (by omega) q).trans
        (Nat.mul_le_mul_right _ (by decide : 8≤24))
  simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using hb

theorem typeD_outer_card_le_proper_index_square (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)]
    (H : Subgroup (CFSG.Models.D r q)) (hH : H≠⊤) :
    Nat.card (Outer (CFSG.Models.D r q))≤H.index^2 := by
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hf : q.exponent≤q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hi : q.order^3≤H.index :=
    (Nat.pow_le_pow_right (by omega : 0<q.order) (by omega : 3≤r-1)).trans
      (typeD_field_power_le_proper_index r hr q H hH)
  have hc : 24≤q.order^5 := (by decide : 24≤2^5).trans (Nat.pow_le_pow_left hq 5)
  calc
    Nat.card (Outer (CFSG.Models.D r q))≤24*q.exponent :=
      typeD_outer_card_le_twentyFour_exponent r hr q
    _ ≤24*q.order := Nat.mul_le_mul_left _ hf
    _ ≤q.order^5*q.order := Nat.mul_le_mul_right _ hc
    _ =q.order^6 := (pow_succ q.order 5).symm
    _ =(q.order^3)^2 := by rw [←pow_mul]
    _ ≤H.index^2 := Nat.pow_le_pow_left hi 2

theorem typeD_order_mul_outer_le_proper_index_log_power
    (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)]
    (H : Subgroup (CFSG.Models.D r q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.D r q)*Nat.card (Outer (CFSG.Models.D r q))≤
      H.index^(4*Nat.log 2 H.index+23) := by
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hi := typeD_field_power_le_proper_index r hr q H hH
  have hm : 2≤H.index := hq.trans
    ((Nat.le_self_pow (by omega : r-1≠0) q.order).trans hi)
  calc
    Nat.card (CFSG.Models.D r q)*Nat.card (Outer (CFSG.Models.D r q))≤
        H.index^(4*Nat.log 2 H.index+10)*H.index^2 := Nat.mul_le_mul
      ((typeD_order_le_matrix_power r hr q).trans
        (matrix_power_le_index_log_power q.order r H.index hq hr hi))
      (typeD_outer_card_le_proper_index_square r hr q H hH)
    _ =H.index^(4*Nat.log 2 H.index+12) := by rw [←pow_add]
    _ ≤H.index^(4*Nat.log 2 H.index+23) := Nat.pow_le_pow_right (by omega) (by omega)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDProperIndexOrderBudget
