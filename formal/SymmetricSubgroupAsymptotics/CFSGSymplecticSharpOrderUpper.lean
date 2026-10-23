import SymmetricSubgroupAsymptotics.CFSGSymplecticCardinality
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveRealization
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! The checked hyperbolic-pair cardinality recurrence supplies a sharper
actual C order upper bound than the full matrix space. This uses the
literal elementary group and its central quotient, in every characteristic. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSharpOrderUpper
open CFSGSymplecticSerreMatrices

private theorem product_factors_le (q n : ℕ) :
    (∏ i ∈ Finset.range n, (q^(2*(i+1))-1)) ≤ q^(n*(n+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    calc
      _ ≤ q^(n*(n+1))*q^(2*(n+1)) := Nat.mul_le_mul ih (Nat.sub_le _ _)
      _ = q^((n+1)*(n+1+1)) := by rw [←pow_add]; congr 1; ring

theorem elementary_card_le_quadratic_power (K : Type) [Field K] [Finite K] (r : ℕ) :
    Nat.card (elementaryRootGroup K r) ≤ Nat.card K^(2*r^2+r) := by
  rw [CFSGSymplecticStabilizerCoordinates.elementary_card]
  calc
    _ ≤ Nat.card K^(r*r)*Nat.card K^(r*(r+1)) :=
      Nat.mul_le_mul_left _ (product_factors_le (Nat.card K) r)
    _ = Nat.card K^(2*r^2+r) := by rw [←pow_add]; congr 1; ring

theorem typeC_order_le_quadratic_power (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)] : Nat.card (CFSG.Models.C r q) ≤ q.order^(2*r^2+r) := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ,r=s+2 := ⟨r-2,by omega⟩
  let e : CFSG.Models.C (s+2) q ≃* elementaryProjective q.Field (s+2) :=
    serreProjectiveEquivElementaryProjective q.Field (s+1)
  rw [Nat.card_congr e.toEquiv]
  have hquot : Nat.card (elementaryProjective q.Field (s+2)) ≤
      Nat.card (elementaryRootGroup q.Field (s+2)) :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup q.Field (s+2))))
      (QuotientGroup.mk'_surjective _)
  exact hquot.trans (by simpa only [q.card_field] using elementary_card_le_quadratic_power q.Field (s+2))

end SymmetricSubgroupAsymptotics.CFSGSymplecticSharpOrderUpper
