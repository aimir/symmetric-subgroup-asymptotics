import SymmetricSubgroupAsymptotics.MarkedC4PsiAnalysis
import Mathlib.Algebra.BigOperators.Field

/-!
# The discrete layer-cake inequality of the joint `C4` tableau

Let `0 ≤ c₀ ≤ c₁ ≤ ⋯ ≤ c_{t-1} ≤ 1` be the diagonal densities of a tableau,
`nₘ ≥ 0` the physical weights, `N = ∑ nₘ`, and `α ≥ β ≥ 0`.  Then

`(1/4) ∑_{j<m} (c_m - c_j) n_j n_m + (α-β) ∑ n_m min(c_m, 1/4)
   + β ∑ n_m min(c_m, 1/2)  ≤  g_N(α)/4 + g_N(β)/4 + g_N(0)/2`.

This is the layer-cake bound (2.3) of the joint tableau note, proved by
telescoping over the sorted densities: with `P_k = ∑_{m ≥ k} n_m`, each
gap `c_k - c_{k-1}` is split into its parts below `1/4`, between `1/4` and
`1/2`, and above `1/2`, and the integrand at `z = P_k` is bounded by the
corresponding value of `g_N`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- The previous density, with `c_{-1} = 0`. -/
def cPrev (c : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else c (k - 1)

/-- Prefix weights `Q_k = ∑_{j<k} n_j`. -/
def prefixWeight (n : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, n j

theorem prefixWeight_succ (n : ℕ → ℝ) (k : ℕ) :
    prefixWeight n (k + 1) = prefixWeight n k + n k := Finset.sum_range_succ _ _

theorem cPrev_succ (c : ℕ → ℝ) (k : ℕ) : cPrev c (k + 1) = c k := by
  simp [cPrev]

theorem sum_range_sub_cPrev (f : ℝ → ℝ) (c : ℕ → ℝ) (t : ℕ) :
    ∑ k ∈ Finset.range (t + 1), (f (c k) - f (cPrev c k)) = f (c t) - f 0 := by
  induction t with
  | zero => simp [cPrev]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, cPrev_succ]
    ring

/-- Telescoping of a transform: `∑ nₘ φ(cₘ) = ∑ₖ (φ cₖ - φ c_{k-1}) (Q_t - Q_k)`
when `φ 0 = 0`. -/
theorem sum_weight_phi_eq (φ : ℝ → ℝ) (hφ : φ 0 = 0) (c n : ℕ → ℝ) (t : ℕ) :
    ∑ m ∈ Finset.range t, n m * φ (c m) =
      ∑ k ∈ Finset.range t, (φ (c k) - φ (cPrev c k)) *
        (prefixWeight n t - prefixWeight n k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htel := sum_range_sub_cPrev φ c t
    rw [hφ, sub_zero, Finset.sum_range_succ] at htel
    have hsplit : ∑ k ∈ Finset.range t, (φ (c k) - φ (cPrev c k)) *
        (prefixWeight n (t + 1) - prefixWeight n k) =
        ∑ k ∈ Finset.range t, (φ (c k) - φ (cPrev c k)) *
          (prefixWeight n t - prefixWeight n k) +
        n t * ∑ k ∈ Finset.range t, (φ (c k) - φ (cPrev c k)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [prefixWeight_succ]
      ring
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hsplit, prefixWeight_succ]
    have : n t * φ (c t) = n t * (∑ k ∈ Finset.range t, (φ (c k) - φ (cPrev c k)) +
        (φ (c t) - φ (cPrev c t))) := by rw [htel]
    rw [this]
    ring

/-- The inner telescoping identity `∑_{j<t} (c_t - c_j) n_j = ∑_{k ≤ t} Δ_k Q_k`. -/
theorem sum_gap_prefix_eq (c n : ℕ → ℝ) (t : ℕ) :
    ∑ j ∈ Finset.range t, (c t - c j) * n j =
      ∑ k ∈ Finset.range (t + 1), (c k - cPrev c k) * prefixWeight n k := by
  induction t with
  | zero => simp [prefixWeight]
  | succ t ih =>
    rw [Finset.sum_range_succ (fun k => (c k - cPrev c k) * prefixWeight n k) (t + 1), ← ih,
      cPrev_succ]
    calc ∑ j ∈ Finset.range (t + 1), (c (t + 1) - c j) * n j
        = ∑ j ∈ Finset.range (t + 1), ((c t - c j) * n j + (c (t + 1) - c t) * n j) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ∑ j ∈ Finset.range (t + 1), (c t - c j) * n j +
            (c (t + 1) - c t) * prefixWeight n (t + 1) := by
          rw [Finset.sum_add_distrib, prefixWeight, Finset.mul_sum]
      _ = _ := by
          rw [Finset.sum_range_succ (fun j => (c t - c j) * n j)]
          ring

/-- Telescoping of the tableau entropy. -/
theorem sum_pairs_eq (c n : ℕ → ℝ) (t : ℕ) :
    ∑ m ∈ Finset.range t, ∑ j ∈ Finset.range m, (c m - c j) * n j * n m =
      ∑ k ∈ Finset.range t, (c k - cPrev c k) *
        ((prefixWeight n t - prefixWeight n k) * prefixWeight n k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hin := sum_gap_prefix_eq c n t
    have hsplit : ∑ k ∈ Finset.range t, (c k - cPrev c k) *
        ((prefixWeight n (t + 1) - prefixWeight n k) * prefixWeight n k) =
        ∑ k ∈ Finset.range t, (c k - cPrev c k) *
          ((prefixWeight n t - prefixWeight n k) * prefixWeight n k) +
        n t * ∑ k ∈ Finset.range t, (c k - cPrev c k) * prefixWeight n k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [prefixWeight_succ]
      ring
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hsplit, prefixWeight_succ]
    have hrow : ∑ j ∈ Finset.range t, (c t - c j) * n j * n t =
        n t * ∑ j ∈ Finset.range t, (c t - c j) * n j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hrow, hin, Finset.sum_range_succ]
    ring

/-! ## The three monotone pieces of a density gap -/

theorem min_steps_nonneg {p x : ℝ} (hpx : p ≤ x) :
    0 ≤ min x (1 / 4) - min p (1 / 4) ∧
    0 ≤ (min x (1 / 2) - min x (1 / 4)) - (min p (1 / 2) - min p (1 / 4)) ∧
    0 ≤ (x - min x (1 / 2)) - (p - min p (1 / 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [min_def] <;> split_ifs <;> linarith

/-- The pointwise integrand bound at one gap. -/
theorem gap_term_le {N Q α β p x : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hQ : 0 ≤ Q) (hQN : Q ≤ N)
    (hpx : p ≤ x) :
    (x - p) * ((N - Q) * Q) / 4 + (α - β) * ((min x (1 / 4) - min p (1 / 4)) * (N - Q)) +
        β * ((min x (1 / 2) - min p (1 / 2)) * (N - Q)) ≤
      (min x (1 / 4) - min p (1 / 4)) * gB N α +
        ((min x (1 / 2) - min x (1 / 4)) - (min p (1 / 2) - min p (1 / 4))) * gB N β +
        ((x - min x (1 / 2)) - (p - min p (1 / 2))) * gB N 0 := by
  obtain ⟨ha, hb, he⟩ := min_steps_nonneg hpx
  set a := min x (1 / 4) - min p (1 / 4)
  set b := (min x (1 / 2) - min x (1 / 4)) - (min p (1 / 2) - min p (1 / 4))
  set e := (x - min x (1 / 2)) - (p - min p (1 / 2))
  have hz : 0 ≤ N - Q := by linarith
  have hzN : N - Q ≤ N := by linarith
  have gα := le_gB (B := N) hα hz hzN
  have gβ := le_gB (B := N) hβ hz hzN
  have g0 := le_gB (B := N) (x := 0) le_rfl hz hzN
  rw [show N - (N - Q) = Q by ring] at gα gβ g0
  have hxp : x - p = a + b + e := by simp only [a, b, e]; ring
  have hab : min x (1 / 2) - min p (1 / 2) = a + b := by simp only [a, b]; ring
  rw [hxp, hab]
  nlinarith [mul_le_mul_of_nonneg_left gα ha, mul_le_mul_of_nonneg_left gβ hb,
    mul_le_mul_of_nonneg_left g0 he]

/-! ## The layer-cake inequality -/

/-- **Layer cake (2.3).**  For sorted densities `0 ≤ c₀ ≤ ⋯ ≤ c_{t-1} ≤ 1`,
nonnegative weights `n`, `N = ∑ nₘ` and `α, β ≥ 0`:

`(1/4) ∑_{j<m} (c_m - c_j) n_j n_m + (α-β) ∑ nₘ min(cₘ,1/4) + β ∑ nₘ min(cₘ,1/2)
  ≤ g_N(α)/4 + g_N(β)/4 + N²/32`. -/
theorem layerCake (c n : ℕ → ℝ) (t : ℕ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hn : ∀ m < t, 0 ≤ n m) (hc0 : ∀ m < t, 0 ≤ c m) (hc1 : ∀ m < t, c m ≤ 1)
    (hmono : ∀ j m, j ≤ m → m < t → c j ≤ c m) :
    (∑ m ∈ Finset.range t, ∑ j ∈ Finset.range m, (c m - c j) * n j * n m) / 4
      + (α - β) * ∑ m ∈ Finset.range t, n m * min (c m) (1 / 4)
      + β * ∑ m ∈ Finset.range t, n m * min (c m) (1 / 2)
    ≤ gB (prefixWeight n t) α / 4 + gB (prefixWeight n t) β / 4 +
        prefixWeight n t ^ 2 / 32 := by
  have hQ : ∀ k ≤ t, 0 ≤ prefixWeight n k ∧ prefixWeight n k ≤ prefixWeight n t := by
    intro k hk
    constructor
    · exact Finset.sum_nonneg (fun j hj => hn j (by rw [Finset.mem_range] at hj; omega))
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      intro j hj _
      exact hn j (Finset.mem_range.mp hj)
  have hN : 0 ≤ prefixWeight n t := (hQ t le_rfl).1
  have hgα := gB_nonneg hN hα
  have hgβ := gB_nonneg hN hβ
  have hg0 : gB (prefixWeight n t) 0 = prefixWeight n t ^ 2 / 16 := gB_zero _ hN
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simp only [Finset.range_zero, Finset.sum_empty, zero_div, mul_zero, add_zero]
    positivity
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hE := sum_pairs_eq c n (s + 1)
  have h1 : ∑ m ∈ Finset.range (s + 1), n m * min (c m) (1 / 4) =
      ∑ k ∈ Finset.range (s + 1), (min (c k) (1 / 4) - min (cPrev c k) (1 / 4)) *
        (prefixWeight n (s + 1) - prefixWeight n k) :=
    sum_weight_phi_eq (fun x => min x (1 / 4)) (by norm_num) c n (s + 1)
  have h2 : ∑ m ∈ Finset.range (s + 1), n m * min (c m) (1 / 2) =
      ∑ k ∈ Finset.range (s + 1), (min (c k) (1 / 2) - min (cPrev c k) (1 / 2)) *
        (prefixWeight n (s + 1) - prefixWeight n k) :=
    sum_weight_phi_eq (fun x => min x (1 / 2)) (by norm_num) c n (s + 1)
  rw [hE, h1, h2]
  set N := prefixWeight n (s + 1)
  -- the pointwise bounds
  have hprev : ∀ k < s + 1, cPrev c k ≤ c k := by
    intro k hk
    unfold cPrev
    split_ifs with h
    · exact hc0 k hk
    · exact hmono (k - 1) k (by omega) hk
  have hsum := Finset.sum_le_sum (s := Finset.range (s + 1)) (fun k hk =>
    gap_term_le (N := N) (Q := prefixWeight n k) hα hβ
      (hQ k (by rw [Finset.mem_range] at hk; omega)).1
      (hQ k (by rw [Finset.mem_range] at hk; omega)).2
      (hprev k (Finset.mem_range.mp hk)))
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul] at hsum
  -- the telescoped totals
  have ta : ∑ k ∈ Finset.range (s + 1), (min (c k) (1 / 4) - min (cPrev c k) (1 / 4)) =
      min (c s) (1 / 4) - min 0 (1 / 4) :=
    sum_range_sub_cPrev (fun x => min x (1 / 4)) c s
  have tb : ∑ k ∈ Finset.range (s + 1), ((min (c k) (1 / 2) - min (c k) (1 / 4)) -
      (min (cPrev c k) (1 / 2) - min (cPrev c k) (1 / 4))) =
      (min (c s) (1 / 2) - min (c s) (1 / 4)) - (min 0 (1 / 2) - min 0 (1 / 4)) :=
    sum_range_sub_cPrev (fun x => min x (1 / 2) - min x (1 / 4)) c s
  have te : ∑ k ∈ Finset.range (s + 1), ((c k - min (c k) (1 / 2)) -
      (cPrev c k - min (cPrev c k) (1 / 2))) =
      (c s - min (c s) (1 / 2)) - (0 - min 0 (1 / 2)) :=
    sum_range_sub_cPrev (fun x => x - min x (1 / 2)) c s
  rw [ta, tb, te] at hsum
  have hcs1 := hc1 s (by omega)
  have m4 : min (0 : ℝ) (1 / 4) = 0 := min_eq_left (by norm_num)
  have m2 : min (0 : ℝ) (1 / 2) = 0 := min_eq_left (by norm_num)
  rw [m4, m2] at hsum
  have hA : min (c s) (1 / 4) - 0 ≤ 1 / 4 := by
    have := min_le_right (c s) (1 / 4); linarith
  have hB : (min (c s) (1 / 2) - min (c s) (1 / 4)) - (0 - 0) ≤ 1 / 4 := by
    simp only [min_def]; split_ifs <;> linarith
  have hC : (c s - min (c s) (1 / 2)) - (0 - 0) ≤ 1 / 2 := by
    simp only [min_def]; split_ifs <;> linarith
  rw [hg0] at hsum
  nlinarith [mul_le_mul_of_nonneg_right hA hgα, mul_le_mul_of_nonneg_right hB hgβ,
    mul_le_mul_of_nonneg_right hC (by positivity : (0 : ℝ) ≤ N ^ 2 / 16)]

/-- **Layer cake with diagonal normal ranks.**  If `0 ≤ dₘ ≤ min(nₘ/4, cₘ nₘ)` and
`α ≥ β ≥ 0`, then the tableau entropy `∑_{j<m} (c_m - c_j) n_j d_m` plus the
retained column bound `(α-β) ∑ dₘ + β ∑ min(2dₘ, cₘ nₘ)` is at most
`g_N(α)/4 + g_N(β)/4 + N²/32`. -/
theorem layerCake_ranks (c n d : ℕ → ℝ) (t : ℕ) {α β : ℝ} (hβ : 0 ≤ β) (hβα : β ≤ α)
    (hn : ∀ m < t, 0 ≤ n m) (hc0 : ∀ m < t, 0 ≤ c m) (hc1 : ∀ m < t, c m ≤ 1)
    (hmono : ∀ j m, j ≤ m → m < t → c j ≤ c m)
    (hd0 : ∀ m < t, 0 ≤ d m) (hd1 : ∀ m < t, d m ≤ n m / 4)
    (hd2 : ∀ m < t, d m ≤ c m * n m) :
    ∑ m ∈ Finset.range t, ∑ j ∈ Finset.range m, (c m - c j) * n j * d m
      + (α - β) * ∑ m ∈ Finset.range t, d m
      + β * ∑ m ∈ Finset.range t, min (2 * d m) (c m * n m)
    ≤ gB (prefixWeight n t) α / 4 + gB (prefixWeight n t) β / 4 +
        prefixWeight n t ^ 2 / 32 := by
  refine le_trans ?_ (layerCake c n t (le_trans hβ hβα) hβ hn hc0 hc1 hmono)
  have e1 : ∑ m ∈ Finset.range t, ∑ j ∈ Finset.range m, (c m - c j) * n j * d m ≤
      (∑ m ∈ Finset.range t, ∑ j ∈ Finset.range m, (c m - c j) * n j * n m) / 4 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hcj : 0 ≤ (c m - c j) * n j :=
      mul_nonneg (sub_nonneg.mpr (hmono j m hj.le hm)) (hn j (by omega))
    have := mul_le_mul_of_nonneg_left (hd1 m hm) hcj
    linarith
  have e2 : ∑ m ∈ Finset.range t, d m ≤ ∑ m ∈ Finset.range t, n m * min (c m) (1 / 4) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_range] at hm
    rw [mul_min_of_nonneg _ _ (hn m hm)]
    exact le_min (by linarith [hd2 m hm]) (by linarith [hd1 m hm])
  have e3 : ∑ m ∈ Finset.range t, min (2 * d m) (c m * n m) ≤
      ∑ m ∈ Finset.range t, n m * min (c m) (1 / 2) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_range] at hm
    rw [mul_min_of_nonneg _ _ (hn m hm)]
    exact le_min (by linarith [min_le_right (2 * d m) (c m * n m)])
      (by linarith [min_le_left (2 * d m) (c m * n m), hd1 m hm])
  have := mul_le_mul_of_nonneg_left e2 (sub_nonneg.mpr hβα)
  have := mul_le_mul_of_nonneg_left e3 hβ
  linarith

end MarkedC4
end SymmetricSubgroupAsymptotics
