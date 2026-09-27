import SymmetricSubgroupAsymptotics.FusionDirectAggregate

/-!
# The varying-width direct continuation row

Each retained original entry is placed at its actual target degree
`n - 2*h + 2*r`. Entries with the same target are still separate summands.
The row sum is exactly the checked wide aggregate. Its decay uses the
explicit original weighted menu bound; this numerical installer supplies
neither that bound nor a physical subgroup-family cover.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ h, Fintype (ι h)]

/-- The same finite width/entry sum, assigned to its literal graph-marker
target. Original widths below 64 are excluded. -/
def fusionWideDirectRow (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ)
    (n m : ℕ) : ℝ :=
  ∑ h ∈ Finset.range (n+1), if 32 ≤ h ∧ 2*h ≤ n then
    ∑ i, if n-2*h+2*r h i = m then
      fusionDirectKernel (n-2*h) h (2*r h i) (D h i) (a h i) (e h i)
    else 0
  else 0

theorem fusionWideDirectRow_nonneg
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ)
    (hD : ∀ h i, 0 ≤ D h i) (ha : ∀ h i, 0 < a h i) (n m : ℕ) :
    0 ≤ fusionWideDirectRow r D a e n m := by
  unfold fusionWideDirectRow
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact fusionDirectKernel_nonneg _ _ _ (hD h i) (ha h i)
    · exact le_rfl
  · exact le_rfl

/-- The prefix bound makes every included target strictly smaller than
the ambient degree. No sign or menu-mass assumptions are needed here. -/
theorem fusionWideDirectRow_forward
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ)
    (hprefix : ∀ h i, 16*r h i ≤ 13*h)
    {n m : ℕ} (hnm : n ≤ m) : fusionWideDirectRow r D a e n m = 0 := by
  unfold fusionWideDirectRow
  apply Finset.sum_eq_zero
  intro h _
  split_ifs with hh
  · apply Finset.sum_eq_zero
    intro i _
    have hp := hprefix h i
    have hne : n-2*h+2*r h i ≠ m := by omega
    exact if_neg hne
  · rfl

/-- Summing over target degrees recovers every retained entry exactly
once, including all entries that happen to have the same target. -/
theorem fusionWideDirectRow_sum
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ)
    (hprefix : ∀ h i, 16*r h i ≤ 13*h) (n : ℕ) :
    (∑ m ∈ Finset.range n, fusionWideDirectRow r D a e n m) =
      fusionWideDirectSum r D a e n := by
  unfold fusionWideDirectRow fusionWideDirectSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : 32 ≤ h ∧ 2*h ≤ n
  · simp only [if_pos hh]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hp := hprefix h i
    have ht : n-2*h+2*r h i < n := by omega
    rw [Finset.sum_eq_single (n-2*h+2*r h i)]
    · simp only [ite_true]
    · intro m _ hm
      exact if_neg (Ne.symm hm)
    · simp only [Finset.mem_range.mpr ht, not_true_eq_false, false_implies]
  · simp only [if_neg hh, Finset.sum_const_zero]

/-- The exact original weighted aggregate controls this same row. The
bound on `Σ D/a` remains an explicit hypothesis at every retained width. -/
theorem fusionWideDirectRow_decay
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ) (H : ℝ)
    (hD : ∀ h i, 0 ≤ D h i) (ha : ∀ h i, 0 < a h i)
    (hprefix : ∀ h i, 16*r h i ≤ 13*h)
    (hgap : ∀ h i, ((2*h : ℕ) : ℝ)/32 ≤ 16*e h i)
    (hmass : ∀ h, 32 ≤ h →
      (∑ i, D h i/a h i) ≤ (2 : ℝ)^((h : ℝ)^2/32+H)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, fusionWideDirectRow r D a e n m) ≤
        C*(2 : ℝ)^(-(n : ℝ)/16) := by
  obtain ⟨C,hC,hbound⟩ :=
    fusionWideDirectSum_eventually r D a e H hD ha hprefix hgap hmass
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with n hn
  rw [fusionWideDirectRow_sum r D a e hprefix n]
  exact hn

/-- Eventual contraction is a numerical consequence, before any bound
on the unknown complete subgroup-count sequence is assumed. -/
theorem fusionWideDirectRow_contractive
    (r : ∀ h, ι h → ℕ) (D a e : ∀ h, ι h → ℝ) (H : ℝ)
    (hD : ∀ h i, 0 ≤ D h i) (ha : ∀ h i, 0 < a h i)
    (hprefix : ∀ h i, 16*r h i ≤ 13*h)
    (hgap : ∀ h i, ((2*h : ℕ) : ℝ)/32 ≤ 16*e h i)
    (hmass : ∀ h, 32 ≤ h →
      (∑ i, D h i/a h i) ≤ (2 : ℝ)^((h : ℝ)^2/32+H)) :
    ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, fusionWideDirectRow r D a e n m) ≤ 1/2 := by
  obtain ⟨C,hC,hbound⟩ :=
    fusionWideDirectRow_decay r D a e H hD ha hprefix hgap hmass
  filter_upwards [hbound,
    eventually_exponential_le_inv_rpow (show (0 : ℝ) < 1/16 by norm_num) 1,
    eventually_ge_atTop (max 1 ⌈2*C⌉₊)] with n hn hexp hlarge
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hlarge
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnC : 2*C ≤ (n : ℝ) := (Nat.le_ceil (2*C)).trans
    (by exact_mod_cast (le_max_right _ _).trans hlarge)
  have heq : -(1/16 : ℝ)*(n : ℝ) = -(n : ℝ)/16 := by ring
  rw [Real.rpow_one, heq] at hexp
  apply hn.trans ((mul_le_mul_of_nonneg_left hexp hC.le).trans ?_)
  rw [mul_one_div]
  exact (div_le_iff₀ hnpos).mpr (by linarith)

end SymmetricSubgroupAsymptotics

end
