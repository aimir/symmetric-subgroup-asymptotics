import SymmetricSubgroupAsymptotics.PrimeGridMiddleBound

/-! Elementary size and positivity facts for the original prime-grid
middle layer; these include the small and rank-zero cases. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem primeGridMiddleWidth_le_card (p r : ℕ) : primeGridMiddleWidth p r≤p^r := by
  calc
    primeGridMiddleWidth p r≤(Finset.univ : Finset (PrimeCosetGrid p r)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = p^r := by rw [Finset.card_univ,primeCosetGrid_card]

theorem primeGridMiddleWidth_pos (p r : ℕ) (hp : 0<p) : 0<primeGridMiddleWidth p r := by
  let D := primeGridSymmetricChains p r hp
  let x : PrimeCosetGrid p r := (primeCosetGridCode p r).symm ⟨0,pow_pos hp r⟩
  have hs := D.start_bound (D.colour x)
  obtain ⟨y,_,hy⟩ := D.rank_surjective (D.colour x) ((r*(p-1))/2)
    (by omega) (by omega)
  exact Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩⟩

/-- The normalized central-binomial expression at an actual prime-power
degree is at least one, including exponent zero. -/
theorem primeGrid_binomial_mass_one_le (p r : ℕ) (hp : 0<p) :
    (1 : ℝ)≤(p : ℝ)^r*((r*(p-1)).choose ((r*(p-1))/2) : ℝ)/(2 : ℝ)^(r*(p-1)) := by
  have hw : 1≤primeGridMiddleWidth p r := primeGridMiddleWidth_pos p r hp
  have h := (Nat.mul_le_mul_left (2^(r*(p-1))) hw).trans
    (primeGridMiddleWidth_binomial p r hp)
  simp only [Nat.mul_one] at h
  have hR : (2 : ℝ)^(r*(p-1))≤
      (p : ℝ)^r*((r*(p-1)).choose ((r*(p-1))/2) : ℝ) := by
    exact_mod_cast h
  exact (le_div_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^(r*(p-1)))).mpr (by simpa using hR)

end SymmetricSubgroupAsymptotics
