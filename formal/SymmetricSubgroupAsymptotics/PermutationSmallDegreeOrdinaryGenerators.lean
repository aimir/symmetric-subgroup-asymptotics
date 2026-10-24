import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.IntervalCases

/-! The exact degree-zero through degree-three bases of the sharp
permutation-generator induction. The full S3 exception is retained.
Only actual group orders and a proper-subgroup index are used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PermutationSmallDegreeOrdinaryGenerators
open FiniteGroupBinaryOrderGenerators

theorem proper_three_card_le_three (J : Subgroup (Equiv.Perm (Fin 3))) (hJ : J≠⊤) :
    Nat.card J≤3 := by
  have hi : 2≤J.index := J.one_lt_index_of_ne_top hJ
  have hprod : J.index*Nat.card J=6 := by
    simpa only [Nat.card_perm,Nat.card_fin] using J.index_mul_card
  have hh : 2*Nat.card J≤6 := (Nat.mul_le_mul_right (Nat.card J) hi).trans_eq hprod
  omega

private theorem rank_le_one_of_card_le_three (G : Type) [Group G] [Finite G]
    (hcard : Nat.card G≤3) : MarkedC4.genRank G≤1 := by
  by_contra h
  have hh : 2≤MarkedC4.genRank G := by omega
  have hp := (Nat.pow_le_pow_right (by decide : 0<2) hh).trans
    ((two_pow_genRank_le_card G).trans hcard)
  norm_num at hp

theorem two_mul_genRank_le_degree (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    (hn : n≤3) (h3 : n=3→J≠⊤) : 2*MarkedC4.genRank J≤n := by
  have hcard : Nat.card J≤n.factorial := by
    have hh := Nat.card_le_card_of_injective
      (Subtype.val : J→Equiv.Perm (Fin n)) Subtype.val_injective
    simpa only [Nat.card_perm,Nat.card_fin] using hh
  interval_cases n
  · have h := genRank_le_of_card_le_two_pow J 0 (by simpa using hcard)
    omega
  · have h := genRank_le_of_card_le_two_pow J 0 (by simpa using hcard)
    omega
  · have h := genRank_le_of_card_le_two_pow J 1 (by simpa using hcard)
    omega
  · have h := rank_le_one_of_card_le_three J (proper_three_card_le_three J (h3 rfl))
    omega

theorem exists_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    (hn : n≤3) (h3 : n=3→J≠⊤) :
    ∃S:Finset J,Subgroup.closure (S:Set J)=⊤ ∧ 2*S.card≤n := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=J)
  refine ⟨S,hgen,?_⟩
  rw [hS]
  exact two_mul_genRank_le_degree n J hn h3

end SymmetricSubgroupAsymptotics.PermutationSmallDegreeOrdinaryGenerators
