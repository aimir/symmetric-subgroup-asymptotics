import SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSpan
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A finite spanning family in the ORIGINAL rational type-A Serre
quotient: r Cartan vectors and the two signed intervals indexed by pairs
of distinct ordered natural coordinates. This is not a dimension input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSGTwistedAIntervalBrackets CFSGSerreChainInvariantSpan

abbrev RootPair (r : ℕ) :=
  {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}
abbrev BasisIndex (r : ℕ) := Fin r ⊕ (Bool × RootPair r)

def rootInterval (r : ℕ) (neg : Bool) (p : RootPair r) : Source r :=
  interval r neg p.val.1.val (p.val.2.val - p.val.1.val)

def basisVectors (r : ℕ) : BasisIndex r → Source r
  | .inl i => cartan r i
  | .inr (neg, p) => rootInterval r neg p

def finiteSpan (r : ℕ) : Submodule ℚ (Source r) :=
  Submodule.span ℚ (Set.range (basisVectors r))

theorem basisVector_mem (r : ℕ) (i : BasisIndex r) : basisVectors r i ∈ finiteSpan r :=
  Submodule.subset_span ⟨i, rfl⟩

theorem cartan_mem_finiteSpan (r : ℕ) (i : Fin r) : cartan r i ∈ finiteSpan r :=
  basisVector_mem r (.inl i)

theorem interval_zero_of_out_of_range (r : ℕ) (neg : Bool) (start n : ℕ)
    (hend : r < start + n) : interval r neg start n = 0 := by
  change chainBracket (simple r neg) start n = 0
  induction n using Nat.twoStepInduction generalizing start with
  | zero => exact chainBracket_zero _ _
  | one =>
    rw [chainBracket_one]
    exact dif_neg (by omega : ¬start < r)
  | more n _ ih =>
    rw [chainBracket_step, ih (start + 1) (by omega), lie_zero]

theorem interval_mem_finiteSpan (r : ℕ) (neg : Bool) (start n : ℕ) :
    interval r neg start n ∈ finiteSpan r := by
  by_cases hn : n = 0
  · subst n
    change chainBracket _ _ 0 ∈ finiteSpan r
    rw [chainBracket_zero]
    exact (finiteSpan r).zero_mem
  by_cases hend : start + n ≤ r
  · let p : RootPair r :=
      ⟨(⟨start, by omega⟩, ⟨start + n, by omega⟩), by change start < start + n; omega⟩
    have hv := basisVector_mem r (.inr (neg, p))
    simpa only [basisVectors, rootInterval, p, Nat.add_sub_cancel_left] using hv
  · rw [interval_zero_of_out_of_range r neg start n (by omega)]
    exact (finiteSpan r).zero_mem

theorem oneSignSpan_le_finiteSpan (r : ℕ) (neg : Bool) :
    oneSignSpan r neg ≤ finiteSpan r := by
  apply Submodule.span_le.mpr
  rintro v (⟨i, rfl⟩ | ⟨⟨start, n⟩, rfl⟩)
  · exact cartan_mem_finiteSpan r i
  · exact interval_mem_finiteSpan r neg start n

theorem finiteSpan_eq_top (r : ℕ) : finiteSpan r = ⊤ := by
  apply top_unique
  rw [← intervalSpan_eq_top r]
  exact sup_le (oneSignSpan_le_finiteSpan r false) (oneSignSpan_le_finiteSpan r true)

def rationalCombination (r : ℕ) : (BasisIndex r → ℚ) →ₗ[ℚ] Source r :=
  Fintype.linearCombination ℚ (basisVectors r)

theorem rationalCombination_surjective (r : ℕ) :
    Function.Surjective (rationalCombination r) := by
  apply LinearMap.range_eq_top.mp
  exact (Fintype.range_linearCombination ℚ (basisVectors r)).trans (finiteSpan_eq_top r)

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
