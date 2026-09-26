import SymmetricSubgroupAsymptotics.FiniteQuotientDerivedIntersection
import SymmetricSubgroupAsymptotics.BinaryMarkedGoursatPeel

/-! Exact row reductions for every actual original normal axis N.
Its derived intersection B=N∩A′ controls the quotient-derived order and
the original quotient-center preimage. The size of N is retained in the
center formula. Exact logarithmic subtraction is used only with a proved
binary-group hypothesis, never with an upper order bound or profile label. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryMarkedGoursatPeel

open FullSubdirectGoursat

variable {A : Type} [Group A] [Finite A] (N : NormalAxis A)

/-- A normal axis in the same whole original A, rather than a subgroup
normal only inside the derived group. -/
def derivedIntersection : NormalAxis A := ⟨N.1 ⊓ commutator A, inferInstance⟩

theorem derivedHead_intersection :
    derivedHead (derivedIntersection N) = derivedHead N := by
  change primeNormalHeadMax 2 ((N.1 ⊓ commutator A) ⊓ commutator A) =
    primeNormalHeadMax 2 (N.1 ⊓ commutator A)
  rw [inf_assoc, inf_idem]

/-- The quotient-derived slope depends only on the actual intersection. -/
theorem derivedSlope_eq_log_div_intersection :
    derivedSlope N = Nat.log 2
      (Nat.card (commutator A) / Nat.card (derivedIntersection N).1) :=
  congrArg (Nat.log 2) (quotientCommutator_card_eq_div_inf N.1)

/-- The center slope retains the entire original axis order, although
the actual center preimage depends only on its derived intersection. -/
theorem centerSlope_eq_log_div_intersection :
    centerSlope N = Nat.log 2
      (Nat.card (quotientCenterPreimage (derivedIntersection N).1) / Nat.card N.1) :=
  congrArg (Nat.log 2) (quotientCenter_card_eq_div_inf_commutator N.1)

private theorem card_eq_two_pow_log {H : Type*} [Group H] [Finite H]
    (hH : IsPGroup 2 H) : Nat.card H = 2 ^ Nat.log 2 (Nat.card H) := by
  obtain ⟨n,hn⟩ := hH.exists_card_eq
  rw [hn, Nat.log_pow (by decide : 1 < 2)]

/-- The subtraction is derived from an exact cardinal product and a
proved prime-power denominator, not from subtracting order upper bounds. -/
theorem derivedSlope_eq_sub_intersection (hA : IsPGroup 2 A) :
    derivedSlope N = Nat.log 2 (Nat.card (commutator A)) -
      orderLog (derivedIntersection N) := by
  rw [derivedSlope_eq_log_div_intersection N]
  change Nat.log 2
    (Nat.card (commutator A) / Nat.card (derivedIntersection N).1) =
      Nat.log 2 (Nat.card (commutator A)) - Nat.log 2 (Nat.card (derivedIntersection N).1)
  have hB := card_eq_two_pow_log (hA.to_subgroup (derivedIntersection N).1)
  rw [hB, Nat.log_div_base_pow, Nat.log_pow (by decide : 1 < 2)]

theorem centerSlope_eq_sub_orderLog (hA : IsPGroup 2 A) :
    centerSlope N = Nat.log 2
      (Nat.card (quotientCenterPreimage (derivedIntersection N).1)) - orderLog N := by
  rw [centerSlope_eq_log_div_intersection N]
  change Nat.log 2
    (Nat.card (quotientCenterPreimage (derivedIntersection N).1) / Nat.card N.1) =
      Nat.log 2 (Nat.card (quotientCenterPreimage (derivedIntersection N).1)) -
        Nat.log 2 (Nat.card N.1)
  have hN := card_eq_two_pow_log (hA.to_subgroup N.1)
  rw [hN, Nat.log_div_base_pow, Nat.log_pow (by decide : 1 < 2)]

end BinaryMarkedGoursatPeel
end SymmetricSubgroupAsymptotics
