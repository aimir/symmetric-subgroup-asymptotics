import SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicReflection
import SymmetricSubgroupAsymptotics.CFSGAlternatingDoubleSwapGeneration

/-! Actual alternating generation on the odd cycle. The four-point
double transposition and its third translate supply an adjacent three-cycle;
all coordinates are in the same literal `ZMod (4*k+1)` action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicDoubleSwap
open CFSGAlternatingCyclicReflection CFSGPermutationCrossSwapWords

theorem rotation_isCycle (k : ℕ) (hk : 1 ≤ k) : (rotation k).IsCycle := by
  letI : Fact (1 < 4 * k + 1) := ⟨by omega⟩
  refine ⟨0, ?_, ?_⟩
  · simpa only [rotation_apply, zero_add] using (one_ne_zero : (1 : Cycle k) ≠ 0)
  · intro y _
    refine ⟨(y.val : ℤ), ?_⟩
    rw [zpow_natCast, rotation_pow_apply, zero_add, ZMod.natCast_zmod_val]

theorem rotation_support (k : ℕ) (hk : 1 ≤ k) :
    (rotation k).support = Finset.univ := by
  letI : Fact (1 < 4 * k + 1) := ⟨by omega⟩
  ext x
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true, rotation_apply]
  intro h
  exact (one_ne_zero : (1 : Cycle k) ≠ 0) (add_left_cancel (h.trans (add_zero x).symm))

def coordinates (k : ℕ) (i : Fin 7) : Cycle k := i.val

theorem coordinates_injective (k : ℕ) (hk : 2 ≤ k) :
    Function.Injective (coordinates k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [coordinates,
    ZMod.val_natCast_of_lt (show i.val < 4 * k + 1 by omega),
    ZMod.val_natCast_of_lt (show j.val < 4 * k + 1 by omega)] using hv

theorem coordinates_shift (k : ℕ) (i : Fin 4) :
    (rotation k ^ 3) (coordinates k ⟨i.val, by omega⟩) =
      coordinates k ⟨i.val + 3, by omega⟩ := by
  rw [rotation_pow_apply]
  simp only [coordinates, Nat.cast_add, Nat.cast_ofNat]

def adjacentDoubleSwap (k : ℕ) : Equiv.Perm (Cycle k) := doubleSwap 0 1 2 3

theorem adjacentDoubleSwap_even (k : ℕ) (hk : 1 ≤ k) :
    adjacentDoubleSwap k ∈ alternatingGroup (Cycle k) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  have h01 : (0 : Cycle k) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    change ((0 : ℕ) : Cycle k).val = ((1 : ℕ) : Cycle k).val at hv
    rw [ZMod.val_natCast_of_lt (show 0 < 4 * k + 1 by omega),
      ZMod.val_natCast_of_lt (show 1 < 4 * k + 1 by omega)] at hv
    omega
  have h23 : (2 : Cycle k) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    change ((2 : ℕ) : Cycle k).val = ((3 : ℕ) : Cycle k).val at hv
    rw [ZMod.val_natCast_of_lt (show 2 < 4 * k + 1 by omega),
      ZMod.val_natCast_of_lt (show 3 < 4 * k + 1 by omega)] at hv
    omega
  change Equiv.Perm.sign (Equiv.swap (0 : Cycle k) 1 * Equiv.swap 2 3) = 1
  rw [map_mul, Equiv.Perm.sign_swap h01, Equiv.Perm.sign_swap h23]
  norm_num

theorem alternating_le_of_rotation_doubleSwap (k : ℕ) (hk : 2 ≤ k)
    (G : Subgroup (Equiv.Perm (Cycle k)))
    (hg : rotation k ∈ G) (ha : adjacentDoubleSwap k ∈ G) :
    alternatingGroup (Cycle k) ≤ G := by
  apply CFSGAlternatingDoubleSwapGeneration.alternating_le_of_cycle_doubleSwap
    G (rotation k) (coordinates k) (coordinates_injective k hk)
  · rw [Nat.card_eq_fintype_card, ZMod.card]
    omega
  · exact rotation_isCycle k (by omega)
  · exact rotation_support k (by omega)
  · exact Equiv.Perm.mem_alternatingGroup.mpr (rotation_even k)
  · exact hg
  · exact ha
  · exact coordinates_shift k
  · change (2 : Cycle k) + 1 = 3
    ring
  · change (3 : Cycle k) + 1 = 4
    ring

end SymmetricSubgroupAsymptotics.CFSGAlternatingCyclicDoubleSwap
