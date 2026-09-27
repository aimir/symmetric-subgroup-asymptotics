import SymmetricSubgroupAsymptotics.MarkerNormalizedKernel
import SymmetricSubgroupAsymptotics.RepeatedMarkerProfileSmall

/-!
# Exact zero-defect marker weights

The actual natural parameter fibre has one even state and two odd states
(only one at rank zero). The single-marker weight retains a supplied actual
pair multiplicity as a mark; replacing it by the ambient rank is identified
only as the larger presentation kernel. No physical pair-moment estimate
or odd error transfer is asserted here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.MarkerZeroDefect

open MarkerGeometry MarkerNormalizedKernel RepeatedMarkerAllocationWeights
  RepeatedMarkerProfileSmall

local instance zeroDefectFinite (N epsilon : ℕ) : Finite (DefectFibre N epsilon 0) :=
  Finite.of_injective profileCode profileCode_injective

def alpha (N : ℕ) : ℝ :=
  (criticalCoefficient N : ℝ) / (analyticParityCoefficient 1 N : ℝ)

def beta (N : ℕ) : ℝ := alpha N / 3

theorem beta_eq (N : ℕ) :
    beta N = (criticalCoefficient N : ℝ) / (3 * (analyticParityCoefficient 1 N : ℝ)) := by
  simp only [beta, alpha, div_div, mul_comm]

/-- Keep the number of actual selected pair positions until physical
incidence has been established. At one marker this is exactly a first mark. -/
def markedKernel {N epsilon : ℕ} (s : Parameters N epsilon) (t : ℕ) : ℝ :=
  (((criticalCoefficient s.M : ℝ) / (analyticParityCoefficient epsilon N : ℝ)) *
    ((binaryGaussianSum s.M : ℝ) / (binaryGaussianSum N : ℝ))) *
    (markerWeight s.g s.f s.q * (markerProfileSum (Q := Fin s.q) s.g : ℝ)) *
    (t.descFactorial s.q : ℝ)

theorem profileKernel_eq_markedKernel {N epsilon : ℕ} (s : Parameters N epsilon) :
    profileKernel s = markedKernel s s.M := rfl

theorem zero_defect_target {N epsilon : ℕ} (s : Parameters N epsilon)
    (hD : s.defect = 0) : s.repeats = 0 ∧ s.M = N := by
  have hk := s.repeats_le_two_defect
  have hb := s.degree_balance
  omega

def emptyState (N epsilon : ℕ) (he : epsilon ≤ 1) : DefectFibre N epsilon 0 :=
  ⟨{ M := N, g := 0, f := epsilon, q := 0,
      parity := he, balance := by omega, q_le_g := by omega,
      q_le_M := by omega, positive_signs := Or.inl rfl },
    by simp [Parameters.defect]⟩

def singleState (N : ℕ) (hN : 1 ≤ N) : DefectFibre N 1 0 :=
  ⟨{ M := N, g := 1, f := 0, q := 1,
      parity := by decide, balance := by omega, q_le_g := by omega,
      q_le_M := hN, positive_signs := Or.inr (by decide) },
    by simp [Parameters.defect]⟩

theorem empty_markedKernel (N epsilon t : ℕ) (he : epsilon ≤ 1) :
    markedKernel (emptyState N epsilon he).val t =
      (criticalCoefficient N : ℝ) / (analyticParityCoefficient epsilon N : ℝ) := by
  have hG : (binaryGaussianSum N : ℝ) ≠ 0 := by
    exact_mod_cast (binaryGaussianSum_pos N).ne'
  have hf : epsilon.factorial = 1 := by
    interval_cases epsilon <;> rfl
  dsimp only [markedKernel, emptyState]
  rw [markerProfileSum_zero_zero]
  simp [markerWeight, hG, hf]

theorem single_markedKernel (N t : ℕ) (hN : 1 ≤ N) :
    markedKernel (singleState N hN).val t = beta N * t := by
  have hG : (binaryGaussianSum N : ℝ) ≠ 0 := by
    exact_mod_cast (binaryGaussianSum_pos N).ne'
  dsimp only [markedKernel, singleState]
  rw [markerProfileSum_one_one]
  norm_num [markerWeight, hG, beta, alpha]
  <;> ring_nf <;> simp

/-- Complete state classification, retaining the literal original fields. -/
theorem zero_state_eq {N epsilon : ℕ} (s : DefectFibre N epsilon 0) :
    s = emptyState N epsilon s.val.parity ∨
      (epsilon = 1 ∧ s.val.M = N ∧ s.val.g = 1 ∧ s.val.f = 0 ∧ s.val.q = 1) := by
  have hM := (zero_defect_target s.val s.property).2
  rcases s.val.zero_defect s.property with h | h
  · left
    apply Subtype.ext
    exact Parameters.ext hM h.1 h.2.1 h.2.2
  · exact Or.inr ⟨h.1, hM, h.2.1, h.2.2.1, h.2.2.2⟩

theorem zero_even_unique (N : ℕ) (s : DefectFibre N 0 0) :
    s = emptyState N 0 (by decide) := by
  rcases zero_state_eq s with h | h
  · exact h
  · omega

theorem zero_odd_eq (N : ℕ) (hN : 1 ≤ N) (s : DefectFibre N 1 0) :
    s = emptyState N 1 (by decide) ∨ s = singleState N hN := by
  rcases zero_state_eq s with h | h
  · exact Or.inl h
  · right
    apply Subtype.ext
    exact Parameters.ext h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem zero_odd_rank_zero_unique (s : DefectFibre 0 1 0) :
    s = emptyState 0 1 (by decide) := by
  rcases zero_state_eq s with h | h
  · exact h
  · have hq := s.val.q_le_M
    omega

theorem zero_even_sum (N : ℕ) (w : Parameters N 0 → ℝ) :
    (∑ s : DefectFibre N 0 0, w s.val) = w (emptyState N 0 (by decide)).val := by
  apply Finset.sum_eq_single (emptyState N 0 (by decide))
  · intro s _ hs
    exact False.elim (hs (zero_even_unique N s))
  · simp

theorem zero_odd_sum (N : ℕ) (hN : 1 ≤ N) (w : Parameters N 1 → ℝ) :
    (∑ s : DefectFibre N 1 0, w s.val) =
      w (emptyState N 1 (by decide)).val + w (singleState N hN).val := by
  have hne : emptyState N 1 (by decide) ≠ singleState N hN := by
    intro h
    have hg := congrArg (fun s : DefectFibre N 1 0 => s.val.g) h
    change 0 = 1 at hg
    omega
  have hu : (Finset.univ : Finset (DefectFibre N 1 0)) =
      {emptyState N 1 (by decide), singleState N hN} := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact zero_odd_eq N hN s
  rw [hu]
  simp [hne]

theorem zero_odd_rank_zero_sum (w : Parameters 0 1 → ℝ) :
    (∑ s : DefectFibre 0 1 0, w s.val) = w (emptyState 0 1 (by decide)).val := by
  apply Finset.sum_eq_single (emptyState 0 1 (by decide))
  · intro s _ hs
    exact False.elim (hs (zero_odd_rank_zero_unique s))
  · simp

/-- In even degree the sole zero-defect state is the untouched even target. -/
theorem defectKernel_even (N : ℕ) : defectKernel N 0 0 = 1 := by
  unfold defectKernel
  rw [zero_even_sum, profileKernel_eq_markedKernel, empty_markedKernel]
  have hc : (criticalCoefficient N : ℝ) ≠ 0 := by
    exact_mod_cast (criticalCoefficient_pos N).ne'
  simp [analyticParityCoefficient, hc]

/-- Exact value of the larger presentation kernel. The factor N is an
ambient pair bound; this identity is not an odd error-transfer estimate. -/
theorem defectKernel_odd (N : ℕ) :
    defectKernel N 1 0 = alpha N + beta N * N := by
  by_cases hN : 1 ≤ N
  · unfold defectKernel
    rw [zero_odd_sum N hN]
    simp only [profileKernel_eq_markedKernel]
    rw [empty_markedKernel, single_markedKernel]
    rfl
  · have h0 : N = 0 := by omega
    subst N
    unfold defectKernel
    rw [zero_odd_rank_zero_sum, profileKernel_eq_markedKernel, empty_markedKernel]
    simp [alpha]

/-- A genuine first mark survives the zero-defect parameter sum unchanged. -/
theorem marked_zero_odd_sum (N t : ℕ) (hN : 1 ≤ N) :
    (∑ s : DefectFibre N 1 0, markedKernel s.val t) = alpha N + beta N * t := by
  calc
    _ = markedKernel (emptyState N 1 (by decide)).val t +
        markedKernel (singleState N hN).val t :=
      zero_odd_sum N hN (fun s => markedKernel s t)
    _ = _ := by rw [empty_markedKernel, single_markedKernel]; rfl

end SymmetricSubgroupAsymptotics.MarkerZeroDefect
