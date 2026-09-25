import SymmetricSubgroupAsymptotics.TraceyTernaryEnvelope
import SymmetricSubgroupAsymptotics.TraceyPrimePowerInput
import SymmetricSubgroupAsymptotics.TraceySylowIndices

/-! Exact ternary conversion and integer aggregation of the published
prime-power factors. The orbit exponents and degree sum are literal
data; constructing the actual Sylow-orbit module filtration remains a
separate group-theoretic theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem traceyPrimePowerFactor_three (t : ℕ) :
    traceyPrimePowerFactor 3 t=⌊(3:ℝ)^t/Real.sqrt (Real.pi*(t:ℝ))⌋₊ := by
  unfold traceyPrimePowerFactor
  norm_num only [Nat.cast_ofNat,show (3:ℝ)-1=2 by norm_num]
  rw [Real.sqrt_div (by norm_num),Real.sqrt_mul (by positivity),
    Real.sqrt_mul Real.pi_pos.le]
  congr 1
  have h2 : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  by_cases ht : t=0
  · subst t; simp
  · have ht' : Real.sqrt (t:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero ht)).ne'
    have hp : Real.sqrt Real.pi≠0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    field_simp

/-- A finite list of original Sylow orbit degrees may be combined with
the floor kept inside the local module dimension. -/
theorem traceyTernaryPrimePower_sum {ι : Type*} [Fintype ι]
    (j : ι→ℕ) (k s : ℕ) (hk : 0<k) (hkj : ∀i,k≤j i)
    (hs : ∑i,3^j i=s) :
    ∑i,traceyPrimePowerFactor 3 (j i)≤
      ⌊(s:ℝ)/Real.sqrt (Real.pi*(k:ℝ))⌋₊ := by
  apply Nat.le_floor
  push_cast
  calc
    ∑i,(traceyPrimePowerFactor 3 (j i):ℝ)≤
        ∑i,(3:ℝ)^j i/Real.sqrt (Real.pi*(k:ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [traceyPrimePowerFactor_three]
      refine (Nat.floor_le (by positivity)).trans ?_
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hkj i) Real.pi_pos.le)
    _=(s:ℝ)/Real.sqrt (Real.pi*(k:ℝ)) := by
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast hs

theorem traceyTernaryPrimePower_weighted_sum {ι : Type*} [Fintype ι]
    (a : ℕ) (j : ι→ℕ) (k s : ℕ) (hk : 0<k) (hkj : ∀i,k≤j i)
    (hs : ∑i,3^j i=s) :
    ∑i,a*traceyPrimePowerFactor 3 (j i)≤
      a*⌊(s:ℝ)/Real.sqrt (Real.pi*(k:ℝ))⌋₊ := by
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left a (traceyTernaryPrimePower_sum j k s hk hkj hs)

/-- The complete numerical aggregation now applies to the actual
Sylow orbits of any original finite transitive action. Only the actual
module-filtration step is still required to apply it to a character head. -/
theorem traceyTernarySylow_weighted_sum {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [Finite X] [MulAction.IsPretransitive G X]
    (P : Sylow 3 G) [Fintype (MulAction.orbitRel.Quotient P X)]
    (a : ℕ) (hk : 0<(Nat.card X).factorization 3) :
    ∃ j : MulAction.orbitRel.Quotient P X→ℕ,
      (∀o,(MulAction.orbit P o.out).ncard=3^j o) ∧
      (∀o,(Nat.card X).factorization 3≤j o) ∧
      ∑o,a*traceyPrimePowerFactor 3 (j o)≤
        a*⌊(Nat.card X:ℝ)/Real.sqrt (Real.pi*((Nat.card X).factorization 3:ℝ))⌋₊ := by
  obtain ⟨j,hj,hcard,hs⟩ := traceySylow_orbit_degrees 3 P (X:=X)
  exact ⟨j,hcard,hj,traceyTernaryPrimePower_weighted_sum a j
    ((Nat.card X).factorization 3) (Nat.card X) hk hj hs⟩

end SymmetricSubgroupAsymptotics
