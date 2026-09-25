import SymmetricSubgroupAsymptotics.PrimeLayerVanishing

/-! Aggregate the relative heads along a literal ambient-normal
filtration. Every section keeps its actual ambient quotient action. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]
variable {A : Type*} [Group A] [Finite A]

/-- Chief-series and block-kernel filtrations can be bounded layer by
layer without replacing relative heads by absolute subgroup ranks. -/
theorem primeRelativeHead_filtration_le
    (N : ℕ → Subgroup A) [∀ i,(N i).Normal]
    (hzero : N 0=⊥) (hstep : ∀ i,N i≤N (i+1)) (n : ℕ) :
    Module.finrank (ZMod p) (primeRelativeCharacters p (N n)) ≤
      ∑ i ∈ Finset.range n,
        Module.finrank (ZMod p) (primeRelativeCharacters p
          (normalChainQuotient (N i) (N (i+1)))) := by
  induction n with
  | zero =>
    have hN : Subsingleton (N 0) := by rw [hzero]; infer_instance
    letI := hN
    simpa only [Finset.range_zero,Finset.sum_empty,Nat.le_zero] using
      primeRelativeHead_perfect p (N 0)
  | succ n ih =>
    have h := primeRelativeHead_chain_le (N n) (N (n+1)) p (hstep n)
    rw [Finset.sum_range_succ]
    exact h.trans (Nat.add_le_add_right ih _)

/-- A local bound for each actual layer installs directly in the same
filtration; vanishing layers may be given the literal bound zero. -/
theorem primeRelativeHead_filtration_bounds
    (N : ℕ → Subgroup A) [∀ i,(N i).Normal]
    (hzero : N 0=⊥) (hstep : ∀ i,N i≤N (i+1)) (c : ℕ → ℕ) (n : ℕ)
    (hc : ∀ i<n,Module.finrank (ZMod p) (primeRelativeCharacters p
      (normalChainQuotient (N i) (N (i+1))))≤c i) :
    Module.finrank (ZMod p) (primeRelativeCharacters p (N n))≤∑ i∈Finset.range n,c i := by
  apply (primeRelativeHead_filtration_le p N hzero hstep n).trans
  exact Finset.sum_le_sum (fun i hi => hc i (Finset.mem_range.mp hi))

end SymmetricSubgroupAsymptotics
