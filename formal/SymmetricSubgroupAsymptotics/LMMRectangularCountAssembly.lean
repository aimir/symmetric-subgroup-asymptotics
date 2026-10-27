import SymmetricSubgroupAsymptotics.LMMHalfDegreeCountRecurrence

/-! Numerical assembly for an actual labelled minimal-block cover.
The local weight is independently known data: it must not contain the
unknown transitive count at the current or any other degree. Only the
single smaller top count in the final recurrence is recursive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace SymmetricSubgroupAsymptotics.LMMRectangularCountAssembly

theorem uniform_of_two_regimes (cost : ℕ → ℕ → ℝ)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ r t : ℕ,
      R ≤ r → 2 ≤ r → 2 ≤ t → cost r t ≤ ε * ((r*t : ℕ) : ℝ)^2)
    (hbounded : ∀ R : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ r t : ℕ,
      2 ≤ r → r < R → T ≤ t → 2 ≤ t → cost r t ≤ ε * ((r*t : ℕ) : ℝ)^2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ r t : ℕ,
      2 ≤ r → 2 ≤ t → N ≤ r*t → cost r t ≤ ε * ((r*t : ℕ) : ℝ)^2 := by
  intro ε hε
  obtain ⟨R₀,hR⟩ := hlarge ε hε
  let R := max 2 R₀
  obtain ⟨T₀,hT⟩ := hbounded R ε hε
  let T := max 2 T₀
  refine ⟨R*T,?_⟩
  intro r t hr ht hn
  by_cases hlocal : R ≤ r
  · exact hR r t ((le_max_right _ _).trans hlocal) hr ht
  · have htop : T ≤ t := by
      by_contra hsmall
      have hh : r*t < R*T :=
        (Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hlocal) (by omega : 0<t)).trans
          (Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hsmall)
            (by have hp := le_max_left 2 R₀; omega : 0<R))
      omega
    exact hT r t hr (Nat.lt_of_not_ge hlocal) ((le_max_right _ _).trans htop) ht

def degreeTerm (b : ℕ → ℕ → ℕ) (n r : ℕ) : ℕ :=
  if 2 ≤ r ∧ 2 ≤ n/r ∧ r*(n/r)=n then b r (n/r) else 0

def nodeWeight (A : ℕ) (b : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  n.factorial^(A*(Nat.log 2 n+2)^2) *
    (1 + ∑ r ∈ Finset.range (n+1), degreeTerm b n r)

/-- Includes a primitive/frame factorial-polylog factor, all actual
factorizations n=r*t, and the additive primitive branch. -/
theorem nodeWeight_eventually (A : ℕ) (b : ℕ → ℕ → ℕ)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ r t : ℕ,
      2 ≤ r → 2 ≤ t → N ≤ r*t →
        (b r t : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (nodeWeight A b n : ℝ) ≤ (2 : ℝ)^(ε*(n : ℝ)^2) := by
  obtain ⟨N,hN⟩ := hb (ε/3) (by positivity)
  filter_upwards [eventually_ge_atTop N,
    FactorialUniformPolylogSubquadraticCount.factorial_budget_eventually A (ε/3) (by positivity),
    LMMHalfDegreeCountRecurrence.exponential_prefactor_eventually (ε/3) (by positivity)]
    with n hn hfactor hpref
  let E : ℝ := (2 : ℝ)^((ε/3)*(n : ℝ)^2)
  have hE : 1 ≤ E := Real.one_le_rpow (by norm_num) (by positivity)
  have hterm (r : ℕ) : (degreeTerm b n r : ℝ) ≤ E := by
    dsimp only [degreeTerm]
    split_ifs with h
    · obtain ⟨hr,ht,heq⟩ := h
      simpa only [heq] using hN r (n/r) hr ht (by omega)
    · simpa only [Nat.cast_zero] using (show (0 : ℝ) ≤ E by linarith only [hE])
  have hsum : (∑ r ∈ Finset.range (n+1), (degreeTerm b n r : ℝ)) ≤
      ((n : ℝ)+1)*E := by
    calc
      _ ≤ ∑ _r ∈ Finset.range (n+1), E := Finset.sum_le_sum (fun r _ => hterm r)
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have hsum' : 1 + (∑ r ∈ Finset.range (n+1), (degreeTerm b n r : ℝ)) ≤
      ((n : ℝ)+2)*E := by nlinarith only [hsum,hE]
  have hnonneg : 0 ≤ 1 + (∑ r ∈ Finset.range (n+1), (degreeTerm b n r : ℝ)) := by positivity
  have hbound : (nodeWeight A b n : ℝ) ≤ E*E*E := by
    unfold nodeWeight
    push_cast
    calc
      _ ≤ E*(((n : ℝ)+2)*E) := mul_le_mul hfactor hsum' hnonneg (by positivity)
      _ ≤ E*(E*E) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpref (by positivity)) (by positivity)
      _ = _ := by ring
  have hcube : E*E*E = (2 : ℝ)^(ε*(n : ℝ)^2) := by
    dsimp only [E]
    rw [←Real.rpow_add (by norm_num : (0 : ℝ)<2),
      ←Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 1
    ring
  exact hbound.trans hcube.le

/-- Final numerical interface. Its recurrence must come from a complete
actual labelled cover; the theorem does not assert that cover. -/
theorem subquadratic_of_labelled_cover {ι : ℕ → Type} [∀ n,Fintype (ι n)]
    (A : ℕ) (b : ℕ → ℕ → ℕ)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ r t : ℕ,
      2 ≤ r → 2 ≤ t → N ≤ r*t →
        (b r t : ℝ) ≤ (2 : ℝ)^(ε*((r*t : ℕ) : ℝ)^2))
    (hcover : ∀ n : ℕ, 2 ≤ n → Nat.card (ι n) ≤
      nodeWeight A b n * (1 + ∑ k ∈ Finset.range (n/2+1), Nat.card (ι k))) :
    SubquadraticMenuIndexCount ι :=
  LMMHalfDegreeCountRecurrence.subquadratic_of_half_degree_recurrence
    (nodeWeight A b) (nodeWeight_eventually A b hb) hcover

end SymmetricSubgroupAsymptotics.LMMRectangularCountAssembly
