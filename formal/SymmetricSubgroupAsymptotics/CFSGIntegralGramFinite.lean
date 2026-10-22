import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

/-! An injective integer Gram embedding has finite norm level sets.
The proof bounds its actual output coordinates and pulls back a finite
box. It never enumerates the roots or computes a catalogue. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGIntegralGramFinite
open scoped BigOperators Matrix

 theorem integer_square_bounds (z : ℤ) (k : ℕ) (hz : z^2≤(k:ℤ)) :
    -(k:ℤ)≤z ∧ z≤(k:ℤ) := by
  have ha : (abs z)≤z^2 := by
    by_cases h0 : z=0
    · subst z
      norm_num
    · have hp : 0<(abs z) := abs_pos.mpr h0
      have hi : 0≤(abs z)-1 := by omega
      have hm := mul_nonneg (abs_nonneg z) hi
      nlinarith [sq_abs z]
  exact abs_le.mp (ha.trans hz)

 theorem finite_energy_level {m n : Type*} [Fintype m] [Fintype n]
    (T : Matrix m n ℤ) (hT : Function.Injective T.mulVec) (k : ℕ) :
    {x : n→ℤ | ∑j,(T*ᵥx) j^2=(k:ℤ)}.Finite := by
  classical
  have hb : {y : m→ℤ | ∀j,y j∈Set.Icc (-(k:ℤ)) (k:ℤ)}.Finite :=
    Set.Finite.pi' (fun _=>Set.finite_Icc _ _)
  have hp : (T.mulVec⁻¹' {y : m→ℤ | ∀j,y j∈Set.Icc (-(k:ℤ)) (k:ℤ)}).Finite :=
    Set.Finite.preimage hT.injOn hb
  apply hp.subset
  intro x hx
  change ∀j,(T*ᵥx) j∈Set.Icc (-(k:ℤ)) (k:ℤ)
  intro j
  have hj : (T*ᵥx) j^2≤(k:ℤ) := by
    calc
      (T*ᵥx) j^2≤∑i,(T*ᵥx) i^2 :=
        Finset.single_le_sum (fun i _=>sq_nonneg ((T*ᵥx) i)) (Finset.mem_univ j)
      _=(k:ℤ) := hx
  exact integer_square_bounds _ k hj

end SymmetricSubgroupAsymptotics.CFSGIntegralGramFinite
