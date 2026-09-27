import SymmetricSubgroupAsymptotics.BinaryOriginalWidePhysical
import SymmetricSubgroupAsymptotics.BinaryOriginalFinitePrefixPhysical

/-!
# Every actual binary orbit of degree at least 1024

The power degree is derived from the actual transitive binary orbit image.
The two finite-prefix degrees and the uniform wide sector cover the same
original unmarked subgroup family by an upper union, without uniqueness or
disjointness assumptions. Their original-weight rows are added literally.
The complementary action and all correlations remain unrestricted.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryOriginalLargePhysical

/-- No power-degree chart or order bound is part of sector membership. -/
def physicalFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ x : Fin n, 1024 ≤ Nat.card (MulAction.orbit H x) ∧
    IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x)}

/-- The actual orbit image is transitive, so its orbit has binary power
cardinality even when the complete original subgroup is not binary. -/
theorem orbit_card_eq_two_pow {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hP : IsPGroup 2 (FusionActualOrbitCharts.orbitImage H x)) :
    ∃ k : ℕ, Nat.card (MulAction.orbit H x)=2^k := by
  let w := Nat.card (MulAction.orbit H x)
  letI : Nonempty (MulAction.orbit H x) := ⟨⟨x,MulAction.mem_orbit_self x⟩⟩
  have hwpos : 0<w := Nat.card_pos
  let V := FusionActualOrbitCharts.chartAction H x (show Nat.card (MulAction.orbit H x)=w from rfl)
  letI : MulAction.IsPretransitive V (Fin w) :=
    FusionActualOrbitCharts.chartAction_transitive H x rfl
  have hV : IsPGroup 2 V := FusionActualOrbitCharts.chartAction_isPGroup H x rfl 2 hP
  let y : Fin w := ⟨0,hwpos⟩
  obtain ⟨k,hk⟩ := hV.card_orbit y
  have hc : Nat.card (MulAction.orbit V y)=w := by
    rw [MulAction.orbit_eq_univ V y]
    exact (Nat.card_congr (Equiv.Set.univ (Fin w))).trans (Nat.card_fin w)
  exact ⟨k,hc.symm.trans hk⟩

/-- Literal coverage by the already installed two sectors. No counting
estimate or assumed power-degree property enters this implication. -/
theorem cover {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ physicalFamily n) :
    H ∈ BinaryOriginalFinitePrefixPhysical.physicalFamily n ∨
      H ∈ BinaryOriginalWidePhysical.physicalFamily n := by
  obtain ⟨x,hlarge,hP⟩ := hH
  obtain ⟨k,hk⟩ := orbit_card_eq_two_pow H x hP
  have hk10 : 10≤k := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    simpa only [hk, show (2:ℕ)^10=1024 from rfl] using hlarge
  by_cases hten : k=10
  · subst k
    left
    refine ⟨0,x,?_,hP⟩
    simpa only [BinaryOriginalFinitePrefixPhysical.halfWidth,
      BinaryOriginalFinitePrefixPhysical.pairExponent, Fin.val_zero, Nat.add_zero] using hk
  by_cases heleven : k=11
  · subst k
    left
    refine ⟨1,x,?_,hP⟩
    simpa only [BinaryOriginalFinitePrefixPhysical.halfWidth,
      BinaryOriginalFinitePrefixPhysical.pairExponent] using hk
  · right
    refine ⟨2^(k-1),⟨?_,?_⟩,x,?_,hP⟩
    · rw [Nat.log_pow (by decide : 1<2)]
    · rw [Nat.log_pow (by decide : 1<2)]
      omega
    · rw [hk, Nat.mul_comm 2, ← pow_succ, Nat.sub_add_cancel (by omega : 1≤k)]

/-- The original subgroup itself is counted, and overlaps are allowed. -/
theorem card_le_sum (n : ℕ) :
    Nat.card (physicalFamily n) ≤
      Nat.card (BinaryOriginalFinitePrefixPhysical.physicalFamily n) +
        Nat.card (BinaryOriginalWidePhysical.physicalFamily n) := by
  let A : Bool → Set (Subgroup (Equiv.Perm (Fin n))) := fun b =>
    if b then BinaryOriginalWidePhysical.physicalFamily n
    else BinaryOriginalFinitePrefixPhysical.physicalFamily n
  have hc := fusionPhysicalUnion_card_le (physicalFamily n) A (by
    intro H hH
    rcases cover H hH with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩)
  simpa [A, add_comm] using hc

/-- The two original rows retain all original action/normal summands. -/
def directRow (n m : ℕ) : ℝ :=
  BinaryOriginalFinitePrefixPhysical.directRow n m + binaryOriginalWideRow n m

theorem directRow_nonneg (n m : ℕ) : 0 ≤ directRow n m :=
  add_nonneg (BinaryOriginalFinitePrefixPhysical.directRow_nonneg n m)
    (binaryOriginalWideRow_nonneg n m)

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : directRow n m=0 := by
  rw [directRow, BinaryOriginalFinitePrefixPhysical.directRow_forward hnm,
    binaryOriginalWideRow_forward hnm, add_zero]

/-- The single intrinsic large-binary-orbit sector has a proved direct
forward recurrence, with no class or coarse subgroup-growth premise. -/
theorem direct_recurrence (n : ℕ) (hn : 2048≤n) :
    (Nat.card (physicalFamily n):ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m:ℝ)/exactBenchmark m) := by
  have hc : (Nat.card (physicalFamily n):ℝ) ≤
      (Nat.card (BinaryOriginalFinitePrefixPhysical.physicalFamily n):ℝ) +
        (Nat.card (BinaryOriginalWidePhysical.physicalFamily n):ℝ) := by
    exact_mod_cast card_le_sum n
  have hb := div_le_div_of_nonneg_right hc (exactBenchmark_pos n).le
  rw [add_div] at hb
  have hs := add_le_add (BinaryOriginalFinitePrefixPhysical.direct_recurrence n hn)
    (BinaryOriginalWidePhysical.direct_recurrence n)
  simpa only [directRow, add_mul, Finset.sum_add_distrib] using hb.trans hs

theorem directRow_decay :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, directRow n m) ≤ C*(2:ℝ)^(-κ*(n:ℝ)) := by
  obtain ⟨C₁,κ,hC₁,hκ,hprefix⟩ := BinaryOriginalFinitePrefixPhysical.directRow_decay
  obtain ⟨C₂,hC₂,hwide⟩ := binaryOriginalWideRow_decay
  refine ⟨C₁+C₂,min κ (1/16),add_pos hC₁ hC₂,lt_min hκ (by norm_num),?_⟩
  filter_upwards [hprefix,hwide] with n hp hw
  have hfirst : (2:ℝ)^(-κ*(n:ℝ)) ≤ (2:ℝ)^(-min κ (1/16)*(n:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (Nat.cast_nonneg n)
  have hsecond : (2:ℝ)^(-(n:ℝ)/16) ≤ (2:ℝ)^(-min κ (1/16)*(n:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right
      (neg_le_neg (min_le_right κ (1/16))) (Nat.cast_nonneg n : (0:ℝ)≤n)
    nlinarith
  calc
    _ = (∑ m ∈ Finset.range n, BinaryOriginalFinitePrefixPhysical.directRow n m) +
        ∑ m ∈ Finset.range n, binaryOriginalWideRow n m := by
      simp only [directRow, Finset.sum_add_distrib]
    _ ≤ C₁*(2:ℝ)^(-κ*(n:ℝ)) + C₂*(2:ℝ)^(-(n:ℝ)/16) := add_le_add hp hw
    _ ≤ C₁*(2:ℝ)^(-min κ (1/16)*(n:ℝ)) + C₂*(2:ℝ)^(-min κ (1/16)*(n:ℝ)) :=
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

theorem filtered_direct_recurrence (n : ℕ) (hn : 2048≤n)
    (P : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily n // P H.1}:ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m:ℝ)/exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily n // P H.1} ≤ Nat.card (physicalFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence n hn)

end SymmetricSubgroupAsymptotics.BinaryOriginalLargePhysical

end
