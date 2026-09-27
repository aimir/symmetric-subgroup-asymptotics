import SymmetricSubgroupAsymptotics.BinaryOriginalSmallPairPhysical
import SymmetricSubgroupAsymptotics.BinaryOriginalLargePhysical

/-!
# Every actual binary orbit of degree at least 32

The finite degrees 32 through 512 and the intrinsic large-orbit sector
cover the literal original subgroup family by an upper union. The binary
power degree is derived from the original orbit image. Both complete
original action/normal rows are retained, including their original weights.
The complementary action and all correlations remain unrestricted.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryOriginalNoncriticalPhysical

/-- Sector membership concerns an actual original orbit. It does not
require the whole subgroup or its complementary action to be binary. -/
def physicalFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ x : Fin n, 32 ≤ Nat.card (MulAction.orbit H x) ∧
    IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x)}

/-- Every intermediate degree is one of the five literal finite widths,
because the actual binary transitive orbit image forces a power degree. -/
theorem cover {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ physicalFamily n) :
    H ∈ BinaryOriginalSmallPairPhysical.physicalFamily n ∨
      H ∈ BinaryOriginalLargePhysical.physicalFamily n := by
  obtain ⟨x,h32,hP⟩ := hH
  by_cases hlarge : 1024 ≤ Nat.card (MulAction.orbit H x)
  · exact Or.inr ⟨x,hlarge,hP⟩
  obtain ⟨k,hk⟩ := BinaryOriginalLargePhysical.orbit_card_eq_two_pow H x hP
  have hk5 : 5 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [hk, show (2:ℕ)^5=32 from rfl] using h32
  have hk10 : k < 10 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
    change (2:ℕ)^k < 1024
    rw [← hk]
    omega
  let t : Fin 5 := ⟨k-5,by omega⟩
  have he : BinaryOriginalSmallPairPhysical.pairExponent t + 1 = k := by
    dsimp [BinaryOriginalSmallPairPhysical.pairExponent,t]
    omega
  left
  refine ⟨t,x,?_,hP⟩
  rw [hk]
  change (2:ℕ)^k = 2*2^(BinaryOriginalSmallPairPhysical.pairExponent t)
  rw [Nat.mul_comm 2, ← pow_succ, he]

/-- The bound counts original subgroups, with overlaps permitted. -/
theorem card_le_sum (n : ℕ) :
    Nat.card (physicalFamily n) ≤
      Nat.card (BinaryOriginalSmallPairPhysical.physicalFamily n) +
        Nat.card (BinaryOriginalLargePhysical.physicalFamily n) := by
  let A : Bool → Set (Subgroup (Equiv.Perm (Fin n))) := fun b =>
    if b then BinaryOriginalLargePhysical.physicalFamily n
    else BinaryOriginalSmallPairPhysical.physicalFamily n
  have hc := fusionPhysicalUnion_card_le (physicalFamily n) A (by
    intro H hH
    rcases cover H hH with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩)
  simpa [A, add_comm] using hc

/-- All original representative/normal contributions are retained even
when several summands reach the same smaller ambient degree. -/
def directRow (n m : ℕ) : ℝ :=
  BinaryOriginalSmallPairPhysical.directRow n m +
    BinaryOriginalLargePhysical.directRow n m

theorem directRow_nonneg (n m : ℕ) : 0 ≤ directRow n m :=
  add_nonneg (BinaryOriginalSmallPairPhysical.directRow_nonneg n m)
    (BinaryOriginalLargePhysical.directRow_nonneg n m)

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : directRow n m=0 := by
  rw [directRow, BinaryOriginalSmallPairPhysical.directRow_forward hnm,
    BinaryOriginalLargePhysical.directRow_forward hnm, add_zero]

/-- The intrinsic noncritical binary-orbit sector has an actual forward
recurrence without a class bound or coarse subgroup-growth premise. -/
theorem direct_recurrence (n : ℕ) (hn : 2048≤n) :
    (Nat.card (physicalFamily n):ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m:ℝ)/exactBenchmark m) := by
  have hc : (Nat.card (physicalFamily n):ℝ) ≤
      (Nat.card (BinaryOriginalSmallPairPhysical.physicalFamily n):ℝ) +
        (Nat.card (BinaryOriginalLargePhysical.physicalFamily n):ℝ) := by
    exact_mod_cast card_le_sum n
  have hb := div_le_div_of_nonneg_right hc (exactBenchmark_pos n).le
  rw [add_div] at hb
  have hs := add_le_add
    (BinaryOriginalSmallPairPhysical.direct_recurrence n (by omega))
    (BinaryOriginalLargePhysical.direct_recurrence n hn)
  simpa only [directRow, add_mul, Finset.sum_add_distrib] using hb.trans hs

theorem directRow_decay :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, directRow n m) ≤ C*(2:ℝ)^(-κ*(n:ℝ)) := by
  obtain ⟨C₁,κ₁,hC₁,hκ₁,hsmall⟩ := BinaryOriginalSmallPairPhysical.directRow_decay
  obtain ⟨C₂,κ₂,hC₂,hκ₂,hlarge⟩ := BinaryOriginalLargePhysical.directRow_decay
  refine ⟨C₁+C₂,min κ₁ κ₂,add_pos hC₁ hC₂,lt_min hκ₁ hκ₂,?_⟩
  filter_upwards [hsmall,hlarge] with n hs hl
  have hfirst : (2:ℝ)^(-κ₁*(n:ℝ)) ≤ (2:ℝ)^(-min κ₁ κ₂*(n:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (Nat.cast_nonneg n)
  have hsecond : (2:ℝ)^(-κ₂*(n:ℝ)) ≤ (2:ℝ)^(-min κ₁ κ₂*(n:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (Nat.cast_nonneg n)
  calc
    _ = (∑ m ∈ Finset.range n, BinaryOriginalSmallPairPhysical.directRow n m) +
        ∑ m ∈ Finset.range n, BinaryOriginalLargePhysical.directRow n m := by
      simp only [directRow, Finset.sum_add_distrib]
    _ ≤ C₁*(2:ℝ)^(-κ₁*(n:ℝ)) + C₂*(2:ℝ)^(-κ₂*(n:ℝ)) := add_le_add hs hl
    _ ≤ C₁*(2:ℝ)^(-min κ₁ κ₂*(n:ℝ)) + C₂*(2:ℝ)^(-min κ₁ κ₂*(n:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hC₁.le)
        (mul_le_mul_of_nonneg_left hsecond hC₂.le)
    _ = _ := by ring

theorem directRow_contractive :
    ∀ᶠ n : ℕ in atTop, (∑ m ∈ Finset.range n, directRow n m) ≤ 1/2 := by
  obtain ⟨C,κ,hC,hκ,hbound⟩ := directRow_decay
  filter_upwards [hbound, eventually_exponential_le_inv_rpow hκ 1,
    eventually_ge_atTop (max 1 ⌈2*C⌉₊)] with n hn hexp hlarge
  have hn1 : 1≤n := (le_max_left _ _).trans hlarge
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hnC : 2*C≤(n:ℝ) := (Nat.le_ceil (2*C)).trans
    (by exact_mod_cast (le_max_right _ _).trans hlarge)
  rw [Real.rpow_one] at hexp
  apply hn.trans ((mul_le_mul_of_nonneg_left hexp hC.le).trans ?_)
  rw [mul_one_div]
  exact (div_le_iff₀ hnpos).mpr (by linarith)

/-- Arbitrary ownership exclusions retain the same row by literal
inclusion of original subgroups, without a naturality condition on P. -/
theorem filtered_direct_recurrence (n : ℕ) (hn : 2048≤n)
    (P : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily n // P H.1}:ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m:ℝ)/exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily n // P H.1} ≤ Nat.card (physicalFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence n hn)

end SymmetricSubgroupAsymptotics.BinaryOriginalNoncriticalPhysical

end
