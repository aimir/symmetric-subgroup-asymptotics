import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall
import SymmetricSubgroupAsymptotics.BinaryNoncriticalActionRankGap
import SymmetricSubgroupAsymptotics.BinaryTerminalPermutationRank

/-! Rank and terminal-defect bounds for the same thirteen original
noncritical colors used by the physical Hall consumer. The C4 color here
is its actual translation range on ZMod4; no identification with a separate
Fin4 generator tuple or with that tuple's normalizer is made.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall

theorem cyclicFourOriginal_rank_le_one :
    Module.finrank (ZMod 2) (PrimeCharacters 2 CyclicFourOriginal) ≤ 1 := by
  have h := BinaryCarrierMixedRankGap.cyclicFour_rank_le_one
  rw [primeCharacter_finrank_congr 2 cyclicFourEquiv] at h
  exact h

/-- The gap belongs to each literal target action on its original points. -/
theorem action_rank_gap (t : Target) :
    Module.finrank (ZMod 2) (PrimeCharacters 2 (action t)) + 1 ≤
      Nat.card (points t) / 2 := by
  cases t with
  | none =>
      have h := cyclicFourOriginal_rank_le_one
      change Module.finrank (ZMod 2) (PrimeCharacters 2 CyclicFourOriginal) + 1 ≤
        Nat.card (ZMod 4) / 2
      norm_num only [Nat.card_zmod]
      omega
  | some t => exact BinaryNoncriticalActionRankGap.original_carrier_rank_gap t

/-- These are marks of the original complete noncritical subgroup H.
They are established before any epimorphism pullback used to count tails. -/
theorem original_noncritical_marks
    {X : Type} [Finite X] (a : ℕ) (m : CarrierTarget → ℕ)
    (labels : OrbitProfilePoints points (multiplicity a m) ≃ X)
    (H : Subgroup (Equiv.Perm X)) (hH : IsPGroup 2 H)
    (hfull : OrbitProfileFullOn action labels H)
    (t : Target) (j : Fin (multiplicity a m t)) :
    (Module.finrank (ZMod 2) (PrimeCharacters 2 H) + 1 ≤ Nat.card X / 2) ∧
      (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) ≤ Nat.card X / 2) :=
  ⟨(hfull.fullBlock t j).rank_add_one_le_half hH (action_rank_gap t),
    terminalRestrictedInflationKernel_literal_permutation_le_half H hH⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall
