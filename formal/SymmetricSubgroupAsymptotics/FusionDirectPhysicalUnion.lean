import SymmetricSubgroupAsymptotics.FusionDirectKernelAssembly
import SymmetricSubgroupAsymptotics.FusionPhysicalUnion

/-!
# The actual shifted first-moment continuation row

An entry of original width `2*h` and marker width `v` continues at
`n-2*h+v`, with its exact original-weight coefficient. The marker must be
strictly smaller than the original width. This is an exact finite sum
identity and a physical counting theorem, with no hot term or coarse input.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A direct entry is assigned to its actual shifted target degree. -/
def fusionFiniteDirectRow {ι : Type*} [Fintype ι] (h v : ι → ℕ)
    (D a e : ι → ℝ) (n m : ℕ) : ℝ :=
  ∑ i, if 2*h i ≤ n ∧ n-2*h i+v i = m then
    fusionDirectKernel (n-2*h i) (h i) (v i) (D i) (a i) (e i) else 0

theorem fusionFiniteDirectRow_nonneg {ι : Type*} [Fintype ι]
    (h v : ι → ℕ) (D a e : ι → ℝ)
    (hD : ∀ i, 0≤D i) (ha : ∀ i, 0<a i) (n m : ℕ) :
    0≤fusionFiniteDirectRow h v D a e n m := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact fusionDirectKernel_nonneg _ _ _ (hD i) (ha i)
  · exact le_rfl

/-- Strict marker savings give a genuinely forward row, including its
zero extension at ambient degrees smaller than the original width. -/
theorem fusionFiniteDirectRow_forward {ι : Type*} [Fintype ι]
    (h v : ι → ℕ) (D a e : ι → ℝ) (hv : ∀ i, v i < 2*h i)
    {n m : ℕ} (hnm : n ≤ m) : fusionFiniteDirectRow h v D a e n m = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : ¬(2*h i≤n ∧ n-2*h i+v i=m) := by
    have := hv i
    omega
  simp only [if_neg hi]

/-- Exact finite-row assembly for any function of the retained target
degree. Distinct normals or actions reaching the same degree are summed. -/
theorem fusionFiniteDirectRow_weighted_sum {ι : Type*} [Fintype ι]
    (h v : ι → ℕ) (D a e : ι → ℝ) (hv : ∀ i, v i < 2*h i)
    (f : ℕ → ℝ) (n : ℕ) (hn : ∀ i, 2*h i≤n) :
    ∑ m ∈ Finset.range n, fusionFiniteDirectRow h v D a e n m * f m =
      ∑ i, fusionDirectKernel (n-2*h i) (h i) (v i) (D i) (a i) (e i) *
        f (n-2*h i+v i) := by
  simp only [fusionFiniteDirectRow, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hi : n-2*h i+v i < n := by have := hv i; have := hn i; omega
  rw [Finset.sum_eq_single (n-2*h i+v i)]
  · rw [if_pos ⟨hn i, rfl⟩]
  · intro m _ hm
    have hne : ¬(2*h i≤n ∧ n-2*h i+v i=m) := by omega
    simp only [if_neg hne, zero_mul]
  · simp [Finset.mem_range.mpr hi]

section PhysicalMenu

variable {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Fin (2*h i))))

/-- Every original action and every literal normal remains a separate
summand, with the actual original action normalizer as divisor. -/
def fusionPhysicalDirectRow
    (v : ∀ i, {N : Subgroup (U i) // N.Normal} → ℕ)
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ) (n m : ℕ) : ℝ :=
  fusionFiniteDirectRow (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => v j.1 j.2) (fun j => D j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor h U j.1) (fun j => e j.1 j.2) n m

theorem fusionPhysicalDirectRow_nonneg
    (v : ∀ i, {N : Subgroup (U i) // N.Normal} → ℕ)
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hD : ∀ i N, 0≤D i N) (n m : ℕ) :
    0≤fusionPhysicalDirectRow h U v D e n m :=
  fusionFiniteDirectRow_nonneg (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => v j.1 j.2) (fun j => D j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor h U j.1) (fun j => e j.1 j.2)
    (fun j => hD j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos h U j.1) n m

theorem fusionPhysicalDirectRow_forward
    (v : ∀ i, {N : Subgroup (U i) // N.Normal} → ℕ)
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hv : ∀ i N, v i N < 2*h i) {n m : ℕ} (hnm : n ≤ m) :
    fusionPhysicalDirectRow h U v D e n m = 0 :=
  fusionFiniteDirectRow_forward (fun j : FusionPhysicalMenuAxis h U => h j.1)
    (fun j => v j.1 j.2) (fun j => D j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor h U j.1) (fun j => e j.1 j.2)
    (fun j => hv j.1 j.2) hnm

/-- Complete literal physical coverage yields the direct shifted
recurrence. The only quantitative inputs are local envelopes and first
same-source moments; the complete original weighted row is the conclusion. -/
theorem fusionPhysicalUnion_direct_recurrence
    (n : ℕ) (hn : ∀ i, 2*h i≤n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (U i × Equiv.Perm (Fin (n-2*h i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionCanonicalFamily (U i) (hn i) (P i))
    (v : ∀ i, {N : Subgroup (U i) // N.Normal} → ℕ)
    (D e : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (Φ : ∀ i, {N : Subgroup (U i) // N.Normal} →
      Subgroup (Equiv.Perm (Fin (n-2*h i))) → ℝ)
    (hv : ∀ i N, v i N < 2*h i) (hD : ∀ i N, 0≤D i N)
    (henvelope : ∀ i N J, fusionSurvivingEpiCount (U i) (P i) N J ≤
      fusionLocalFactor (n-2*h i) (h i) (v i N) (D i N) (e i N)*Φ i N J)
    (hmoment : ∀ i N, (∑ J, Φ i N J) ≤
      (subgroupCount (n-2*h i+v i N) : ℝ)) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, fusionPhysicalDirectRow h U v D e n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  have hcard := fusionPhysicalUnion_card_le F
    (fun i => FusionCanonicalFamily (U i) (hn i) (P i)) hcover
  have hcardR : (Nat.card F : ℝ) ≤
      ∑ i, (Nat.card (FusionCanonicalFamily (U i) (hn i) (P i)) : ℝ) := by
    exact_mod_cast hcard
  have hlocal (i : ι) :
      (Nat.card (FusionCanonicalFamily (U i) (hn i) (P i)) : ℝ)/exactBenchmark n ≤
      ∑ N : {N : Subgroup (U i) // N.Normal},
        fusionDirectKernel (n-2*h i) (h i) (v i N) (D i N)
          (fusionPhysicalMenuDivisor h U i) (e i N) *
          ((subgroupCount (n-2*h i+v i N) : ℝ)/exactBenchmark (n-2*h i+v i N)) := by
    rw [fusionCanonicalFamily_card]
    have hx := fusionPhysical_direct_bound (U i) (n-2*h i) (P i) (hP i)
      (v i) (D i) (e i) (Φ i) (hD i) (henvelope i) (hmoment i)
    simpa only [Nat.sub_add_cancel (hn i), fusionPhysicalMenuDivisor] using hx
  calc
    _ ≤ (∑ i, (Nat.card (FusionCanonicalFamily (U i) (hn i) (P i)) : ℝ))/
        exactBenchmark n := div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ i, (Nat.card (FusionCanonicalFamily (U i) (hn i) (P i)) : ℝ)/
        exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ i, ∑ N : {N : Subgroup (U i) // N.Normal},
        fusionDirectKernel (n-2*h i) (h i) (v i N) (D i N)
          (fusionPhysicalMenuDivisor h U i) (e i N) *
          ((subgroupCount (n-2*h i+v i N) : ℝ)/exactBenchmark (n-2*h i+v i N)) :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = _ := by
      unfold fusionPhysicalDirectRow
      rw [fusionFiniteDirectRow_weighted_sum
        (fun j : FusionPhysicalMenuAxis h U => h j.1)
        (fun j => v j.1 j.2) (fun j => D j.1 j.2)
        (fun j => fusionPhysicalMenuDivisor h U j.1) (fun j => e j.1 j.2)
        (fun j => hv j.1 j.2) _ n (fun j => hn j.1)]
      rw [Fintype.sum_sigma]

end PhysicalMenu
end SymmetricSubgroupAsymptotics

end
