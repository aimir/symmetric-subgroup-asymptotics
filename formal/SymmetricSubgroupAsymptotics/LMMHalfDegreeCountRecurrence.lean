import SymmetricSubgroupAsymptotics.FactorialUniformPolylogSubquadraticCount

/-! The purely numerical global counting step. A subquadratic node cost
and ONE recursively selected top of degree at most n/2 give subquadratic
total count. The actual subgroup-cover recurrence must still be proved
before this lemma can discharge LMM; it is not a new endpoint assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace SymmetricSubgroupAsymptotics.LMMHalfDegreeCountRecurrence

private theorem add_two_le_factorial (n : ℕ) (hn : 4 ≤ n) : n + 2 ≤ n.factorial := by
  induction n,hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    calc
      (n + 1) + 2 ≤ (n + 1) * (n + 2) := by nlinarith only [hn]
      _ ≤ (n + 1) * n.factorial := Nat.mul_le_mul_left _ ih
      _ = (n + 1).factorial := (Nat.factorial_succ n).symm

theorem exponential_prefactor_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) + 2 ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ 2) := by
  filter_upwards [FactorialUniformPolylogSubquadraticCount.factorial_budget_eventually 1 ε hε,
    eventually_ge_atTop 4] with n hb hn
  have hp : n + 2 ≤ n.factorial ^ ((Nat.log 2 n + 2) ^ 2) :=
    (add_two_le_factorial n hn).trans (Nat.le_self_pow (pow_ne_zero 2 (by omega)) _)
  have hpR : (n : ℝ) + 2 ≤ (n.factorial : ℝ) ^ ((Nat.log 2 n + 2) ^ 2) := by
    exact_mod_cast hp
  exact hpR.trans (by simpa only [one_mul] using hb)

theorem exists_uniform_exp_bound (a w : ℕ → ℕ)
    (hw : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (w n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ 2))
    (hrec : ∀ n : ℕ, 2 ≤ n →
      a n ≤ w n * (1 + ∑ k ∈ Finset.range (n / 2 + 1), a k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, (a n : ℝ) ≤ B * (2 : ℝ) ^ (ε * (n : ℝ) ^ 2) := by
  have hevent : ∀ᶠ n : ℕ in atTop,
      (w n : ℝ) ≤ (2 : ℝ) ^ ((ε / 4) * (n : ℝ) ^ 2) ∧
      (n : ℝ) + 2 ≤ (2 : ℝ) ^ ((ε / 4) * (n : ℝ) ^ 2) ∧ 2 ≤ n := by
    filter_upwards [hw (ε / 4) (by positivity),
      exponential_prefactor_eventually (ε / 4) (by positivity),eventually_ge_atTop 2]
      with n hn hp htwo
    exact ⟨hn,hp,htwo⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  let B : ℝ := 1 + ∑ k ∈ Finset.range N, (a k : ℝ)
  have hB : 1 ≤ B := by
    have hs : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, (a k : ℝ) := by positivity
    dsimp only [B]
    linarith only [hs]
  refine ⟨B,by linarith only [hB],?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hpow : 1 ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ 2) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hε.le (sq_nonneg _))
    by_cases hlarge : N ≤ n
    · obtain ⟨hwn,hpref,hn⟩ := hN n hlarge
      let P : ℝ := (2 : ℝ) ^ ((ε / 4) * (n : ℝ) ^ 2)
      have hP : 1 ≤ P := Real.one_le_rpow (by norm_num) (by positivity)
      have hBP : 1 ≤ B * P := by
        have hh := mul_le_mul hB hP (by norm_num : (0 : ℝ) ≤ 1) (by linarith only [hB])
        simpa only [one_mul] using hh
      have hterm (k : ℕ) (hk : k ∈ Finset.range (n / 2 + 1)) : (a k : ℝ) ≤ B * P := by
        have hhalf : 2 * k ≤ n := by have hh := Finset.mem_range.mp hk; omega
        have hkn : k < n := by omega
        have hkR : (k : ℝ) ≤ (n : ℝ) / 2 := by
          have hh : 2 * (k : ℝ) ≤ n := by exact_mod_cast hhalf
          linarith only [hh]
        have hs : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by
          have hh := (sq_le_sq₀ (Nat.cast_nonneg k) (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)).mpr hkR
          nlinarith only [hh]
        have hexp : ε * (k : ℝ) ^ 2 ≤ (ε / 4) * (n : ℝ) ^ 2 := by
          nlinarith only [mul_le_mul_of_nonneg_left hs hε.le]
        exact (ih k hkn).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by linarith only [hB]))
      have hsum : (∑ k ∈ Finset.range (n / 2 + 1), (a k : ℝ)) ≤
          ((n / 2 + 1 : ℕ) : ℝ) * (B * P) := by
        calc
          _ ≤ ∑ _k ∈ Finset.range (n / 2 + 1), B * P := Finset.sum_le_sum hterm
          _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      have hcount : ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast (show n / 2 + 1 ≤ n + 1 by omega)
      have hsum' : (∑ k ∈ Finset.range (n / 2 + 1), (a k : ℝ)) ≤
          ((n : ℝ) + 1) * (B * P) := hsum.trans
        (mul_le_mul_of_nonneg_right hcount (by linarith only [hBP]))
      have hone : 1 + (∑ k ∈ Finset.range (n / 2 + 1), (a k : ℝ)) ≤
          ((n : ℝ) + 2) * (B * P) := by nlinarith only [hsum',hBP]
      have hrecR : (a n : ℝ) ≤ (w n : ℝ) *
          (1 + ∑ k ∈ Finset.range (n / 2 + 1), (a k : ℝ)) := by exact_mod_cast hrec n hn
      have hbound : (a n : ℝ) ≤ P * P * (B * P) := by
        calc
          _ ≤ P * (((n : ℝ) + 2) * (B * P)) := hrecR.trans
            (mul_le_mul hwn hone (by positivity) (by positivity))
          _ ≤ P * (P * (B * P)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpref
              (by linarith only [hBP])) (by linarith only [hP])
          _ = _ := by ring
      have hP3 : P * P * P = (2 : ℝ) ^ ((3 * ε / 4) * (n : ℝ) ^ 2) := by
        dsimp only [P]
        rw [←Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ←Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      calc
        (a n : ℝ) ≤ B * (P * P * P) := by nlinarith only [hbound]
        _ = B * (2 : ℝ) ^ ((3 * ε / 4) * (n : ℝ) ^ 2) := by rw [hP3]
        _ ≤ B * (2 : ℝ) ^ (ε * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by nlinarith only [mul_nonneg hε.le (sq_nonneg (n : ℝ))]))
              (by linarith only [hB])
    · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      have hh : (a n : ℝ) ≤ ∑ k ∈ Finset.range N, (a k : ℝ) :=
        Finset.single_le_sum (f := fun k => (a k : ℝ)) (fun _ _ => Nat.cast_nonneg _) hmem
      have hb : (a n : ℝ) ≤ B := by dsimp only [B]; linarith only [hh]
      exact hb.trans (le_mul_of_one_le_right (by linarith only [hB]) hpow)

theorem subquadratic_of_half_degree_recurrence
    {ι : ℕ → Type} [∀ n,Fintype (ι n)] (w : ℕ → ℕ)
    (hw : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (w n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ 2))
    (hrec : ∀ n : ℕ, 2 ≤ n →
      Nat.card (ι n) ≤ w n * (1 + ∑ k ∈ Finset.range (n / 2 + 1), Nat.card (ι k))) :
    SubquadraticMenuIndexCount ι := by
  intro ε hε
  exact exists_uniform_exp_bound (fun n => Nat.card (ι n)) w hw hrec ε hε

end SymmetricSubgroupAsymptotics.LMMHalfDegreeCountRecurrence
