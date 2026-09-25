import SymmetricSubgroupAsymptotics.EvenCriticalAsymptotic
import SymmetricSubgroupAsymptotics.OddCriticalAsymptotic

/-!
# The complete critical-family theorem

The family consists of actual subgroups on the usual labelled set Fin n,
with every full central lift and the permitted odd marker. Its asymptotic
supplies the matching lower bound for all subgroups. It does not bound the
noncritical complement and therefore does not assert T1.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

def EvenCriticalSubgroupsOn (R n : ℕ) : Type :=
  AssembledOrbitProfilesOn
    (fun p : (criticalProfiles R) ↦ p.1.multiplicity)
    (fun p ↦ OrbitProfileFull (m := p.1.multiplicity) criticalActionSubgroup 1)
    (Fin n)

def OddCriticalSubgroupsOn (R n : ℕ) : Type :=
  AssembledOrbitProfilesOn (oddCriticalIndexMultiplicity R)
    (fun p ↦ OrbitProfileFull (m := oddCriticalIndexMultiplicity R p)
      oddCriticalActionSubgroup 1)
    (Fin n)

/-- All full subgroups on the specified critical action profiles, on Fin n.
The two branches are literal labelled subgroup families of the same S_n. -/
def CriticalSubgroups (n : ℕ) : Type :=
  if n % 2 = 0 then EvenCriticalSubgroupsOn (n / 2) n
  else OddCriticalSubgroupsOn (n / 2) n

instance (n : ℕ) : Finite (CriticalSubgroups n) := by
  unfold CriticalSubgroups
  split <;>
    simp only [EvenCriticalSubgroupsOn, OddCriticalSubgroupsOn, AssembledOrbitProfilesOn] <;>
      infer_instance

theorem criticalSubgroups_even (R : ℕ) : CriticalSubgroups (2 * R) = EvenCriticalSubgroups R := by
  simp only [CriticalSubgroups, Nat.mul_mod_right, ↓reduceIte,
    Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  rfl

theorem criticalSubgroups_odd (R : ℕ) : CriticalSubgroups (2 * R + 1) = OddCriticalSubgroups R := by
  simp only [CriticalSubgroups, show (2 * R + 1) % 2 = 1 by omega,
    show ¬ (1 : ℕ) = 0 by omega, ↓reduceIte, show (2 * R + 1) / 2 = R by omega]
  rfl

theorem criticalSubgroups_card_le_subgroupCount (n : ℕ) :
    Nat.card (CriticalSubgroups n) ≤ subgroupCount n := by
  unfold CriticalSubgroups subgroupCount
  split <;> exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- The complete critical-family count has exponentially small relative
error, with one constant and threshold for both parities. The rate is chosen
conservatively to make the passage from half-degree to degree explicit. -/
theorem criticalSubgroups_relative_error :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |(Nat.card (CriticalSubgroups n) : ℝ) / exactBenchmark n - 1| ≤
        K * (2 : ℝ) ^ (-(n : ℝ) / 96) := by
  obtain ⟨A, hA, NA, hNA, heven⟩ := evenCriticalSubgroups_relative_error
  obtain ⟨B, hB, NB, hNB, hodd⟩ := oddCriticalSubgroups_relative_error
  refine ⟨max A B, lt_of_lt_of_le hA (le_max_left _ _),
    2 * max NA NB, by omega, ?_⟩
  intro n hn
  have hne : NA ≤ n / 2 := by omega
  have hno : NB ≤ n / 2 := by omega
  have hr1 : 1 ≤ n / 2 := by omega
  have hdeg : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 3 * (n / 2) by omega)
  have hexp : (2 : ℝ) ^ (-((n / 2 : ℕ) : ℝ) / 32) ≤
      (2 : ℝ) ^ (-(n : ℝ) / 96) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  by_cases hp : n % 2 = 0
  · have hnrepr : n = 2 * (n / 2) := by omega
    have h := heven (n / 2) hne
    rw [← criticalSubgroups_even, ← hnrepr] at h
    exact h.trans (mul_le_mul (le_max_left A B) hexp (by positivity) (le_of_lt (lt_of_lt_of_le hA (le_max_left _ _))))
  · have hnrepr : n = 2 * (n / 2) + 1 := by omega
    have h := hodd (n / 2) hno
    rw [← criticalSubgroups_odd, ← hnrepr] at h
    exact h.trans (mul_le_mul (le_max_right A B) hexp (by positivity) (le_of_lt (lt_of_lt_of_le hA (le_max_left _ _))))

/-- The complete normalized critical term is bounded at every degree,
including the finite initial segment. This provides a bounded forcing term
for later recurrences without assuming bounded total subgroup counts. -/
theorem criticalSubgroups_normalized_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (Nat.card (CriticalSubgroups n) : ℝ) / exactBenchmark n ≤ C := by
  obtain ⟨K,hK,N,_hN,hbound⟩ := criticalSubgroups_relative_error
  let S : ℝ := ∑ n ∈ Finset.range N,
    (Nat.card (CriticalSubgroups n) : ℝ) / exactBenchmark n
  have hnonneg (n : ℕ) :
      0 ≤ (Nat.card (CriticalSubgroups n) : ℝ) / exactBenchmark n :=
    div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos n).le
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ ↦ hnonneg n)
  refine ⟨1 + K + S, by linarith, ?_⟩
  intro n
  by_cases hn : n < N
  · have hle : (Nat.card (CriticalSubgroups n) : ℝ) / exactBenchmark n ≤ S :=
      Finset.single_le_sum (fun i _ ↦ hnonneg i) (Finset.mem_range.mpr hn)
    linarith
  · have h := (abs_le.mp (hbound n (by omega))).2
    have hp : (2 : ℝ) ^ (-(n : ℝ) / 96) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show -(n : ℝ) / 96 ≤ 0 by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hmul := mul_le_mul_of_nonneg_left hp hK.le
    linarith

/-- The critical family supplies the exponential lower side of T1 for the
actual total subgroup count. No upper bound on other subgroups is used. -/
theorem subgroupCount_critical_lower :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 - K * (2 : ℝ) ^ (-(n : ℝ) / 96) ≤
        (subgroupCount n : ℝ) / exactBenchmark n := by
  obtain ⟨K,hK,N,hN,hbound⟩ := criticalSubgroups_relative_error
  refine ⟨K,hK,N,hN,?_⟩
  intro n hn
  have h := (abs_le.mp (hbound n hn)).1
  have hcard : (Nat.card (CriticalSubgroups n) : ℝ) ≤ subgroupCount n := by
    exact_mod_cast criticalSubgroups_card_le_subgroupCount n
  have hratio := div_le_div_of_nonneg_right hcard (exactBenchmark_pos n).le
  linarith

end SymmetricSubgroupAsymptotics
