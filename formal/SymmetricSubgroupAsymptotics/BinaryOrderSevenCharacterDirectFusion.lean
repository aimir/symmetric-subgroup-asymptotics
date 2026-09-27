import SymmetricSubgroupAsymptotics.BinaryOrderSevenCharacterFusion
import SymmetricSubgroupAsymptotics.BinaryOrderCharacterDirectFusion
import SymmetricSubgroupAsymptotics.BinaryPermutationClassBound

/-!
# Unconditional direct fusion for the binary seven-power class bound

The actual finite permutation class theorem is installed internally. Every
original action and normal retains its chosen order or character entry,
normalizer divisor, exact even prefix and all common-source moments. The
physical family still needs literal coverage by the supplied finite menu.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

private theorem sevenClassInput : BinarySevenPermutationClassInput := by
  intro b P hP
  simpa only [Nat.card_fin] using
    BinaryPermutationClassBound.literal_class_card_pow_seven_le (Fin b) P hP

section Menu

variable {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Fin (2*h i))))
    (C : ∀ i, BinaryOrderSevenCharacterSelection (U i))

/-- The actual original-action/normal sum, installed in its shifted row. -/
def binaryOrderSevenCharacterDirectRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow h U (fun i => (C i).prefixDegree)
    (fun i => (C i).liftConstant) (fun i => (C i).gapParameter) n m

theorem binaryOrderSevenCharacterDirectRow_nonneg (n m : ℕ) :
    0≤binaryOrderSevenCharacterDirectRow h U C n m :=
  fusionPhysicalDirectRow_nonneg h U _ _ _ (fun i => (C i).liftConstant_nonneg) n m

theorem binaryOrderSevenCharacterDirectRow_forward (hh : ∀ i, 0<h i)
    {n m : ℕ} (hnm : n ≤ m) : binaryOrderSevenCharacterDirectRow h U C n m = 0 :=
  fusionPhysicalDirectRow_forward h U _ _ _
    (fun i N => (C i N).prefixDegree_lt (by have := hh i; omega)) hnm

/-- Complete original physical coverage gives a forward first-moment
recurrence with no additive hot error and no coarse-growth hypothesis. -/
theorem binaryOrderSevenCharacterSelection_direct_recurrence
    (hU : ∀ i, IsPGroup 2 (U i))
    (hh : ∀ i, 0<h i) (n : ℕ) (hn : ∀ i, 2*h i≤n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (U i × Equiv.Perm (Fin (n-2*h i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionCanonicalFamily (U i) (hn i) (P i)) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, binaryOrderSevenCharacterDirectRow h U C n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) :=
  fusionPhysicalUnion_direct_recurrence h U n hn F P hP hcover
    (fun i => (C i).prefixDegree) (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) (fun i N J => (C i).momentWeight N J)
    (fun i N => (C i N).prefixDegree_lt (by have := hh i; omega))
    (fun i => (C i).liftConstant_nonneg)
    (fun i => (C i).original_envelope sevenClassInput (hU i) (n-2*h i) (P i))
    (fun i N => by simpa only [pow_one, one_mul] using
      (C i).moment_le N (n-2*h i) 1)

/-- The complete original weighted direct row has a positive exponential
rate. Its proof does not assume total subgroup counts. -/
theorem binaryOrderSevenCharacterDirectRow_decay (hh : ∀ i, 0<h i) :
    ∃ A κ : ℝ, 0<A ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, binaryOrderSevenCharacterDirectRow h U C n m ≤
        A*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => (C j.1).prefixDegree j.2) (fun j => (C j.1 j.2).markerHalf)
    (fun j => (C j.1).liftConstant j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => (C j.1).gapParameter j.2)
    (fun j => (C j.1 j.2).prefixDegree_lt (by have := hh j.1; omega))
    (fun j => (C j.1 j.2).prefixDegree_eq_two_mul)
    (fun j => (C j.1).liftConstant_nonneg j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1)
    (fun j => (C j.1).gapParameter_pos j.2)

/-- Eventual contraction of the same literal row. -/
theorem binaryOrderSevenCharacterDirectRow_contractive (hh : ∀ i, 0<h i) :
    ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, binaryOrderSevenCharacterDirectRow h U C n m ≤ 1/2 :=
  fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => (C j.1).prefixDegree j.2) (fun j => (C j.1 j.2).markerHalf)
    (fun j => (C j.1).liftConstant j.2) (fun j => fusionPhysicalMenuDivisor h U j.1)
    (fun j => (C j.1).gapParameter j.2)
    (fun j => (C j.1 j.2).prefixDegree_lt (by have := hh j.1; omega))
    (fun j => (C j.1 j.2).prefixDegree_eq_two_mul)
    (fun j => (C j.1).liftConstant_nonneg j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1)
    (fun j => (C j.1).gapParameter_pos j.2)

end Menu
end SymmetricSubgroupAsymptotics

end
