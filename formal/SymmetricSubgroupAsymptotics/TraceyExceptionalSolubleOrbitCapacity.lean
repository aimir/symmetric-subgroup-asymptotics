import SymmetricSubgroupAsymptotics.TraceyExceptionalThreeFromRaw
import SymmetricSubgroupAsymptotics.TraceySolublePermutationFormulaProof

/-!
# The aggregate orbit capacity sufficient for the exceptional binary head

The actual consumer of Corollary 3.12 needs neither its binomial indexing
nor the Mersenne prime itself. It needs one soluble subgroup whose orbit
binary parts have sufficiently small sum. This file isolates that strictly
weaker structural target. It does not assert that target unconditionally.

The original raw statement implies the stronger aggregate bound with
constant `12`; the head consumer only needs the displayed `5/16` bound.
The module restriction is on the same original action and subrepresentation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

/-- A module-independent replacement for the full exceptional orbit
description. Only the degree range and odd part used by the head consumer
are requested, and the witness is a literal subgroup of the acting group. -/
def TraceyExceptionalSolubleOrbitCapacityInput : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X],
    24 ≤ Nat.card X → ordCompl[2] (Nat.card X) = 3 →
    HasNoSolubleTransitiveSubgroup G X →
    ∃ N : Subgroup G, IsSolvable N ∧
      16 * (∑ o : MulAction.orbitRel.Quotient N X,
        ordProj[2] (Nat.card o.orbit)) ≤ 5 * Nat.card X

/-- The full raw orbit geometry actually gives a stronger aggregate bound
than the exceptional head requires. No module is involved in this step. -/
theorem tracey_raw_exceptional_soluble_orbit_capacity
    (horbit : TraceyCorollaryThreeTwelveRawInput)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hnone : HasNoSolubleTransitiveSubgroup G X)
    (m : ℕ) (hsize : Nat.card X = 3 * 2 ^ m) :
    ∃ N : Subgroup G, IsSolvable N ∧
      12 * (∑ o : MulAction.orbitRel.Quotient N X,
        ordProj[2] (Nat.card o.orbit)) ≤ Nat.card X := by
  obtain ⟨a, e, t₁, t, N, ha, he, ht, hm, hp, hNsol,
    hcount, index, hcards⟩ := horbit G X hnone m hsize
  have hp2 : 2 ^ a - 1 ≠ 2 := by
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ha
    norm_num at hpow
    omega
  have hpodd : ¬2 ∣ 2 ^ a - 1 := by
    have hh := hp.eq_two_or_odd.resolve_left hp2
    simpa only [Nat.dvd_iff_mod_eq_zero] using
      (by omega : ¬ (2 ^ a - 1) % 2 = 0)
  have hpart : ∀ o : MulAction.orbitRel.Quotient N X,
      ordProj[2] (Nat.card o.orbit) = 2 ^ (t - t₁) := by
    intro o
    rw [hcards o]
    apply tracey_ordProj_odd_mul_two_pow
    · exact Nat.mul_ne_zero (by decide) (pow_ne_zero _ hp.ne_zero)
    · intro hdiv
      rcases Nat.prime_two.dvd_mul.mp hdiv with hh | hh
      · norm_num at hh
      · exact hpodd (Nat.prime_two.dvd_of_dvd_pow hh)
  have hsum :
      (∑ o : MulAction.orbitRel.Quotient N X,
        ordProj[2] (Nat.card o.orbit)) = 2 ^ (e + t) := by
    simp only [hpart, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card, hcount]
    simp only [Nat.cast_id]
    rw [← pow_add]
    congr 1
    omega
  have hea : e * 3 ≤ e * a := Nat.mul_le_mul_left e ha
  have hgap : e + t + 2 ≤ e * a + t := by omega
  have hpow : 4 * 2 ^ (e + t) ≤ 2 ^ (e * a + t) := by
    calc
      4 * 2 ^ (e + t) = 2 ^ (e + t + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ (e * a + t) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hgap
  refine ⟨N, hNsol, ?_⟩
  rw [hsum, hsize, hm]
  nlinarith

/-- Forgetting the raw orbit labels leaves exactly the structural capacity
needed by the binary exceptional head argument. -/
theorem traceyExceptionalSolubleOrbitCapacity_of_raw
    (horbit : TraceyCorollaryThreeTwelveRawInput) :
    TraceyExceptionalSolubleOrbitCapacityInput := by
  intro G X _ _ _ _ _ _ _ ho hnone
  let m := (Nat.card X).factorization 2
  have hsize : Nat.card X = 3 * 2 ^ m := by
    simpa only [ho, m, Nat.mul_comm] using
      (Nat.ordProj_mul_ordCompl_eq_self (Nat.card X) 2).symm
  obtain ⟨N, hNsol, hcap⟩ :=
    tracey_raw_exceptional_soluble_orbit_capacity horbit G X hnone m hsize
  exact ⟨N, hNsol, by omega⟩

/-- The same original module head is controlled from the aggregate orbit
capacity. The soluble-transitive case is already an unconditional formula
consequence and does not need the exceptional capacity hypothesis. -/
theorem traceyBinaryExceptionalThree_of_solubleOrbitCapacity
    (hsol : TraceySolublePermutationFormulaRawInput)
    (hcapacity : TraceyExceptionalSolubleOrbitCapacityInput) :
    TraceyBinaryExceptionalThreeInput := by
  intro G _ _ X _ _ _ _ M hs ho
  by_cases htrans : ∃ N : Subgroup G,
      IsSolvable N ∧ MulAction.IsPretransitive N X
  · obtain ⟨N, hNsol, hNtrans⟩ := htrans
    letI : IsSolvable N := hNsol
    letI : MulAction.IsPretransitive N X := hNtrans
    let m := (Nat.card X).factorization 2
    have hsize : Nat.card X = 3 * 2 ^ m := by
      simpa only [ho, m, Nat.mul_comm] using
        (Nat.ordProj_mul_ordCompl_eq_self (Nat.card X) 2).symm
    have hf := traceySolublePermutation_head_formula hsol N X
      (permutationSubrepresentationRestrict N M)
    rw [hsize] at hf
    have hnum := traceySolubleFormula_three_five_sixteenths
      (by simpa only [← hsize] using hs) hf
    exact (Nat.mul_le_mul_left 16
      (permutationHead_finrank_le_subgroup N M)).trans
      (by simpa only [← hsize] using hnum)
  · have hnone : HasNoSolubleTransitiveSubgroup G X := by
      intro N hN hh
      exact htrans ⟨N, hN, hh⟩
    obtain ⟨N, hNsol, hcap⟩ := hcapacity G X hs ho hnone
    letI : IsSolvable N := hNsol
    exact (Nat.mul_le_mul_left 16
      (tracey_soluble_subgroup_head_le_binary_parts hsol N M)).trans hcap

/-- All soluble module estimates in the reduction are already proved;
only the aggregate exceptional orbit capacity remains as an argument. -/
theorem traceyBinaryExceptionalThree_of_solubleOrbitCapacity_provedSoluble
    (hcapacity : TraceyExceptionalSolubleOrbitCapacityInput) :
    TraceyBinaryExceptionalThreeInput :=
  traceyBinaryExceptionalThree_of_solubleOrbitCapacity
    traceySolublePermutationFormulaRawInput_proved hcapacity

end SymmetricSubgroupAsymptotics
