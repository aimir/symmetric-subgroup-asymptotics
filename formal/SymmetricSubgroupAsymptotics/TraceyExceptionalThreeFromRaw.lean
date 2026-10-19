import SymmetricSubgroupAsymptotics.TraceyCorollaryThreeTwelveRaw
import SymmetricSubgroupAsymptotics.TraceyExceptionalSolubleNumerics
import SymmetricSubgroupAsymptotics.PermutationHeadSubgroupRestriction

/-! The exceptional binary `5/16` head bound is a project deduction from
raw published soluble-module formulae and Corollary 3.12 orbit geometry.
No fractional head estimate is an input. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics

/-- Apply the exact soluble formula on every literal subgroup orbit. -/
theorem tracey_soluble_subgroup_head_le_binary_parts
    (hsol : TraceySolublePermutationFormulaRawInput)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (N : Subgroup G) [IsSolvable N]
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X)) :
    Module.finrank (ZMod 2) (M.toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2))) ≤
      ∑ o : MulAction.orbitRel.Quotient N X, ordProj[2] (Nat.card o.orbit) := by
  apply (permutationHead_finrank_le_subgroup N M).trans
  apply permutationSubrepresentationHead_le_orbit_caps
  intro o S
  letI : MulAction.IsPretransitive N o.orbit := ⟨by
    intro x y
    exact MulAction.exists_smul_eq N x y⟩
  exact (traceySolublePermutation_head_formula hsol N o.orbit S).1

/-- Constructor replacing the formerly imported numerical exceptional
consequence by raw published statements and checked deductions. -/
theorem traceyBinaryExceptionalThree_of_raw
    (hsol : TraceySolublePermutationFormulaRawInput)
    (horbit : TraceyCorollaryThreeTwelveRawInput) :
    TraceyBinaryExceptionalThreeInput := by
  intro G _ _ X _ _ _ _ M hs ho
  let m := (Nat.card X).factorization 2
  have hsize : Nat.card X = 3 * 2 ^ m := by
    simpa only [ho, m, Nat.mul_comm] using
      (Nat.ordProj_mul_ordCompl_eq_self (Nat.card X) 2).symm
  by_cases htrans : ∃ N : Subgroup G,
      IsSolvable N ∧ MulAction.IsPretransitive N X
  · obtain ⟨N, hNsol, hNtrans⟩ := htrans
    letI : IsSolvable N := hNsol
    letI : MulAction.IsPretransitive N X := hNtrans
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
    obtain ⟨a, e, t₁, t, N, ha, he, ht, hm, hp, hNsol,
      hcount, index, hcards⟩ := horbit G X hnone m hsize
    letI : IsSolvable N := hNsol
    have hp2 : 2 ^ a - 1 ≠ 2 := by
      have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ha
      norm_num at hpow
      omega
    have hpodd : ¬2 ∣ 2 ^ a - 1 := by
      have hh := hp.eq_two_or_odd.resolve_left hp2
      simpa only [Nat.dvd_iff_mod_eq_zero] using (by omega :
        ¬ (2 ^ a - 1) % 2 = 0)
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
    have hhead := tracey_soluble_subgroup_head_le_binary_parts hsol N M
    rw [hsum] at hhead
    have hnum := tracey_binomial_orbit_capacity_five_sixteenths a e t ha he
    have hsize' : Nat.card X = 3 * 2 ^ (e * a + t) := by
      simpa only [hm] using hsize
    rw [hsize']
    nlinarith

end SymmetricSubgroupAsymptotics
