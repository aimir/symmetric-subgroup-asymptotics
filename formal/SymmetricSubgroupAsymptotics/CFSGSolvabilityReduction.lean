import SymmetricSubgroupAsymptotics.CFSGClassificationTransport
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Solvability from simple-group order information

A divisor-closed property of group orders reduces solvability to the finite
simple cases by strong induction. In particular, checking even order for the
nonabelian concrete CFSG models would imply odd-order solvability; the original
Feit--Thompson proof need not be imported as an additional hypothesis.

This file proves the reduction. It does not assume or claim the outstanding
even-order facts about the concrete Lie and sporadic models.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

private theorem proper_card_lt {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (hK : K ≠ ⊤) : Nat.card K < Nat.card G := by
  conv_rhs => rw [← K.card_mul_index]
  exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr (Subgroup.one_lt_index_of_ne_top hK)

private theorem quotient_card_lt {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hN : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  conv_rhs => rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
  exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr (N.one_lt_card_iff_ne_bot.mpr hN)

/-- An order property closed under taking divisors reduces solvability to
commutativity of its simple groups. This is an elementary extension induction. -/
theorem solvable_of_simple_order_property
    (P : ℕ → Prop)
    (divisor_closed : ∀ {m n : ℕ}, P n → m ∣ n → P m)
    (simple_commutative : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      P (Nat.card G) → IsMulCommutative G)
    (G : Type) [Group G] [Finite G] (hG : P (Nat.card G)) : IsSolvable G := by
  suffices aux : ∀ n : ℕ, ∀ (H : Type) [Group H] [Finite H],
      Nat.card H = n → P n → IsSolvable H by
    exact aux (Nat.card G) G rfl hG
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H _ _ hcard hP
    classical
    rcases subsingleton_or_nontrivial H with hsub | hnontrivial
    · letI := hsub
      infer_instance
    · letI := hnontrivial
      by_cases hex : ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
      · obtain ⟨N, hnormal, hbot, htop⟩ := hex
        letI := hnormal
        have hN : P (Nat.card N) := divisor_closed (hcard ▸ hP)
          (Subgroup.card_subgroup_dvd_card N)
        have hQ : P (Nat.card (H ⧸ N)) := divisor_closed (hcard ▸ hP)
          ⟨Nat.card N, Subgroup.card_eq_card_quotient_mul_card_subgroup N⟩
        have hnlt : Nat.card N < n := by
          rw [← hcard]
          exact proper_card_lt htop
        have hqlt : Nat.card (H ⧸ N) < n := by
          rw [← hcard]
          exact quotient_card_lt hbot
        letI : IsSolvable N := ih (Nat.card N) hnlt N rfl hN
        letI : IsSolvable (H ⧸ N) := ih (Nat.card (H ⧸ N)) hqlt (H ⧸ N) rfl hQ
        exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
          (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
      · letI : IsSimpleGroup H := ⟨fun N hnormal => by
          by_contra hn
          push Not at hn
          exact hex ⟨N, hnormal, hn.1, hn.2⟩⟩
        exact isSolvable_of_comm
          (isMulCommutative_iff.mp (simple_commutative H (hcard ▸ hP)))

/-- The preceding induction with the concrete CFSG cases exposed. Model
finiteness and simplicity are transported from the classified source. -/
theorem solvable_of_cfsg_order_property
    (hCFSG : CFSG.CFSGClassification) (P : ℕ → Prop)
    (divisor_closed : ∀ {m n : ℕ}, P n → m ∣ n → P m)
    (models : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      P (Nat.card i.Model) → IsMulCommutative i.Model)
    (G : Type) [Group G] [Finite G] (hG : P (Nat.card G)) : IsSolvable G := by
  apply solvable_of_simple_order_property P divisor_closed ?_ G hG
  intro H _ _ _ hH
  let W := simpleModelWitness hCFSG H
  letI := W.finite_model
  letI := W.simple_model
  have hm : P (Nat.card W.index.Model) := by
    rwa [← Nat.card_congr W.equiv.toEquiv]
  exact (isMulCommutative_congr W.equiv).mpr (models W.index hm)

/-- A narrow family-level even-order theorem would suffice to derive
odd-order solvability from CFSG, with no separate solvability assumption. -/
theorem odd_order_solvable_of_cfsg_even_models
    (hCFSG : CFSG.CFSGClassification)
    (models_even : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬ IsMulCommutative i.Model → Even (Nat.card i.Model))
    (G : Type) [Group G] [Finite G] (hG : Odd (Nat.card G)) : IsSolvable G := by
  apply solvable_of_cfsg_order_property hCFSG Odd
    (fun hn hd => Odd.of_dvd_nat hn hd) ?_ G hG
  intro i _ _ hi
  by_contra hnoncomm
  exact hi.not_two_dvd_nat (even_iff_two_dvd.mp (models_even i hnoncomm))

end SymmetricSubgroupAsymptotics.CFSGReduction
