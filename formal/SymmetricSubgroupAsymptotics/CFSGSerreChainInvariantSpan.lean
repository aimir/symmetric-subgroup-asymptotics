import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalRaising

/-! A linear invariant-span argument for chains. Mixed-sign action is
proved inside the original Lie algebra from mixed generator brackets;
no dimension comparison or natural-image faithfulness enters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSerreChainInvariantSpan
open CFSGTwistedAIntervalBrackets
variable {L I : Type} [LieRing L] [LieAlgebra ℚ L]

def chainSpan (x : ℕ → L) (h : I → L) : Submodule ℚ L :=
  Submodule.span ℚ (Set.range h ∪ Set.range (fun p : ℕ × ℕ => chainBracket x p.1 p.2))

theorem cartan_mem (x : ℕ → L) (h : I → L) (i : I) : h i ∈ chainSpan x h :=
  Submodule.subset_span (Or.inl ⟨i, rfl⟩)

theorem interval_mem (x : ℕ → L) (h : I → L) (start n : ℕ) :
    chainBracket x start n ∈ chainSpan x h :=
  Submodule.subset_span (Or.inr ⟨(start, n), rfl⟩)

theorem simple_mem (x : ℕ → L) (h : I → L) (k : ℕ) : x k ∈ chainSpan x h := by
  simpa only [chainBracket_one] using interval_mem x h k 1

theorem stable_of_generators (x : ℕ → L) (h : I → L) (a : L)
    (hH : ∀ i, ⁅a, h i⁆ ∈ chainSpan x h)
    (hX : ∀ start n, ⁅a, chainBracket x start n⁆ ∈ chainSpan x h)
    (v : L) (hv : v ∈ chainSpan x h) : ⁅a, v⁆ ∈ chainSpan x h := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨i, rfl⟩ | ⟨⟨start, n⟩, rfl⟩
    · exact hH i
    · exact hX start n
  | zero => rw [lie_zero]; exact (chainSpan x h).zero_mem
  | add v w _ _ hv hw => rw [lie_add]; exact (chainSpan x h).add_mem hv hw
  | smul a v _ hv => rw [lie_smul]; exact (chainSpan x h).smul_mem a hv

variable (x : ℕ → L) (h : I → L)
  (hfar : ∀ i j, i + 1 < j ∨ j + 1 < i → ⁅x i, x j⁆ = 0)
  (hserre : ∀ i j, i + 1 = j ∨ j + 1 = i → ⁅x i, ⁅x i, x j⁆⁆ = 0)
  (c : I → ℕ → ℚ)
  (hweight : ∀ i j, ⁅h i, x j⁆ = c i j • x j)

include hfar hserre hweight

theorem simple_stable (k : ℕ) (v : L) (hv : v ∈ chainSpan x h) :
    ⁅x k, v⁆ ∈ chainSpan x h := by
  apply stable_of_generators x h (x k) ?_ ?_ v hv
  · intro i
    rw [← lie_skew (x k) (h i), hweight]
    exact (chainSpan x h).neg_mem ((chainSpan x h).smul_mem _ (simple_mem x h k))
  · intro start n
    by_cases hn : n = 0
    · subst n; rw [chainBracket_zero, lie_zero]; exact (chainSpan x h).zero_mem
    · rw [lie_chainBracket_raising x hfar hserre start n k (by omega)]
      split_ifs
      · exact interval_mem x h _ _
      · exact (chainSpan x h).neg_mem (interval_mem x h _ _)
      · exact (chainSpan x h).zero_mem

/-- Cartan action on a chain needs only the generator weights. -/
theorem cartan_interval_mem (i : I) (start n : ℕ) :
    ⁅h i, chainBracket x start n⁆ ∈ chainSpan x h := by
  induction n using Nat.twoStepInduction generalizing start with
  | zero => rw [chainBracket_zero, lie_zero]; exact (chainSpan x h).zero_mem
  | one =>
    rw [chainBracket_one, hweight]
    exact (chainSpan x h).smul_mem _ (simple_mem x h start)
  | more n _ ih =>
    rw [chainBracket_step, leibniz_lie, hweight, smul_lie]
    exact (chainSpan x h).add_mem
      ((chainSpan x h).smul_mem _ (by
        simpa only [chainBracket_step] using interval_mem x h start (n + 2)))
      (simple_stable x h hfar hserre c hweight start _ (ih (start + 1)))

/-- An opposite generator acts into the same Cartan-and-chain span.
This avoids assuming any mixed interval bracket formula or matrix model. -/
theorem opposite_interval_mem (y : L)
    (hmixed : ∀ j, ⁅y, x j⁆ ∈ Submodule.span ℚ (Set.range h))
    (start n : ℕ) : ⁅y, chainBracket x start n⁆ ∈ chainSpan x h := by
  have hc : ∀ v ∈ Submodule.span ℚ (Set.range h), ∀ start n,
      ⁅v, chainBracket x start n⁆ ∈ chainSpan x h := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact cartan_interval_mem x h hfar hserre c hweight i
    | zero => intro start n; rw [zero_lie]; exact (chainSpan x h).zero_mem
    | add v w _ _ hv hw =>
      intro start n; rw [add_lie]
      exact (chainSpan x h).add_mem (hv start n) (hw start n)
    | smul a v _ hv =>
      intro start n; rw [smul_lie]
      exact (chainSpan x h).smul_mem a (hv start n)
  induction n using Nat.twoStepInduction generalizing start with
  | zero => rw [chainBracket_zero, lie_zero]; exact (chainSpan x h).zero_mem
  | one =>
    rw [chainBracket_one]
    exact (Submodule.span_mono Set.subset_union_left) (hmixed start)
  | more n _ ih =>
    rw [chainBracket_step, leibniz_lie]
    exact (chainSpan x h).add_mem
      (hc _ (hmixed start) (start + 1) (n + 1))
      (simple_stable x h hfar hserre c hweight start _ (ih (start + 1)))

end SymmetricSubgroupAsymptotics.CFSGSerreChainInvariantSpan
