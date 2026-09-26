import SymmetricSubgroupAsymptotics.BinaryMarkedGoursatPeel
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalDerivedHead

/-! Automatic carrier-row fields for an actual normal axis containing the
original derived subgroup. All heads retain whole-ambient conjugation.
The optional head calculation requires an actual radical equality, not a
stored profile value. No finite normal catalogue is assumed complete. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryMarkedGoursatPeel

open FullSubdirectGoursat

variable {A : Type} [Group A] [Finite A] (N : NormalAxis A)

/-- Above the actual derived subgroup, the axis maximum is the complete
original derived-normal rank, with its unchanged ambient action. -/
theorem derivedHead_eq_of_commutator_le (hD : commutator A ≤ N.1) :
    derivedHead N = primeDerivedNormalRank 2 A := by
  unfold derivedHead primeDerivedNormalRank
  rw [inf_eq_right.mpr hD]

/-- The literal quotient has trivial derived subgroup. -/
theorem derivedSlope_eq_zero_of_commutator_le (hD : commutator A ≤ N.1) :
    derivedSlope N = 0 := by
  letI : IsMulCommutative (A ⧸ N.1) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hD
  simp only [derivedSlope, commutator_eq_bot, Subgroup.card_bot]
  exact Nat.log_of_lt (by decide : 1 < 2)

/-- The center is the whole original quotient, rather than an abstract
abelian group with a matching order. -/
theorem centerSlope_eq_log_quotient_of_commutator_le (hD : commutator A ≤ N.1) :
    centerSlope N = Nat.log 2 (Nat.card (A ⧸ N.1)) := by
  letI : IsMulCommutative (A ⧸ N.1) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hD
  simp only [centerSlope, Subgroup.center_eq_top, Subgroup.card_top]

/-- One verified original evaluation-kernel containment controls the
second radical of every axis; it is not a generic odd-order deficit. -/
theorem radicalHead_le_derivedHead_of_evaluation_kernel_le
    (hG : (primeAbelianizationGroupMap 2 A).ker ≤ commutator A) :
    radicalHead N ≤ derivedHead N :=
  primeRelativeRadical_head_le_axis_max_of_evaluation_kernel_le 2 N.1 hG

/-- Four actual row fields for the entire abelian-quotient branch. The
only hypotheses are original subgroup containments, not numerical labels. -/
theorem abelianQuotient_row_fields (hD : commutator A ≤ N.1)
    (hG : (primeAbelianizationGroupMap 2 A).ker ≤ commutator A) :
    derivedHead N = primeDerivedNormalRank 2 A ∧
      derivedSlope N = 0 ∧
      centerSlope N = Nat.log 2 (Nat.card (A ⧸ N.1)) ∧
      radicalHead N ≤ derivedHead N :=
  ⟨derivedHead_eq_of_commutator_le N hD,
    derivedSlope_eq_zero_of_commutator_le N hD,
    centerSlope_eq_log_quotient_of_commutator_le N hD,
    radicalHead_le_derivedHead_of_evaluation_kernel_le N hG⟩

/-- A checked literal radical witness gives the exact original index.
This does not infer the witness from equality of recorded row labels. -/
theorem head_index_of_radical_eq_commutator
    (hR : primeRelativeRadical 2 N.1 = commutator A) :
    Nat.card N.1 / Nat.card (commutator A) = 2 ^ head N := by
  have hc := primeRelativeRadical_card_factorization 2 N.1
  rw [hR] at hc
  change Nat.card N.1 = 2 ^ head N * Nat.card (commutator A) at hc
  rw [hc, Nat.mul_div_cancel _ (Nat.card_pos (α := commutator A))]

/-- Consequently a finite order certificate binds the head without a
separate character-space calculation. -/
theorem head_eq_log_index_of_radical_eq_commutator
    (hR : primeRelativeRadical 2 N.1 = commutator A) :
    head N = Nat.log 2 (Nat.card N.1 / Nat.card (commutator A)) := by
  rw [head_index_of_radical_eq_commutator N hR, Nat.log_pow (by decide : 1 < 2)]

end BinaryMarkedGoursatPeel
end SymmetricSubgroupAsymptotics
