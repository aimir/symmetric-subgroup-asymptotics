import Mathlib

/-!
# Three precise asymptotic targets

This file defines the objects and propositions for T1, T2 and T3 in `SPEC.md`.
It supplies no proof of an asymptotic claim. The definitions do not assume
published group theory, certificate acceptance, or the existence of a saddle.
`DefinitionChecks` states the required meaning and positivity obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The number of actual subgroups, with no quotient by conjugacy. -/
def subgroupCount (n : ℕ) : ℕ :=
  Nat.card (Subgroup (Equiv.Perm (Fin n)))

/-- The number of all binary subspaces, summed over every dimension. -/
def binarySubspaceCount (r : ℕ) : ℕ :=
  Nat.card (Submodule (ZMod 2) (Fin r → ZMod 2))

def halfDegree (n : ℕ) : ℕ := n / 2

def parity (n : ℕ) : ℕ := n % 2

/-- Exact rational coefficient of `exp(x/2 + x²/6 + x⁴/384)`. -/
def criticalCoefficient (r : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (r + 1),
    ∑ b ∈ Finset.range (r + 1),
      ∑ d ∈ Finset.range (r + 1),
        if a + 2 * b + 4 * d = r then
          1 / ((2 : ℚ) ^ a * (Nat.factorial a : ℚ) *
            (6 : ℚ) ^ b * (Nat.factorial b : ℚ) *
            (384 : ℚ) ^ d * (Nat.factorial d : ℚ))
        else 0

/-- The shifted coefficient vanishes at rank zero, before natural subtraction. -/
def parityCoefficient (n : ℕ) : ℚ :=
  criticalCoefficient (halfDegree n) +
    if parity n = 1 ∧ 0 < halfDegree n then
      criticalCoefficient (halfDegree n - 1) / 6
    else 0

/-- The exact coefficient benchmark `L_n`. -/
def exactBenchmark (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * (binarySubspaceCount (halfDegree n) : ℝ) *
    (parityCoefficient n : ℝ)

def criticalPolynomial (x : ℝ) : ℝ := x / 2 + x ^ 2 / 6 + x ^ 4 / 384

def saddleMean (x : ℝ) : ℝ := x / 2 + x ^ 2 / 3 + x ^ 4 / 96

def saddleVariance (x : ℝ) : ℝ := x / 2 + 2 * x ^ 2 / 3 + x ^ 4 / 24

/-- A total definition that assumes no root-existence theorem.
For positive `r`, `DefinitionChecks.saddle_positive_unique` requires this
infimum to be the unique positive solution of the saddle equation. -/
def saddleRadius (r : ℕ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ (r : ℝ) ≤ saddleMean x}

/-- The exact-saddle benchmark `Q_n`; the two unused initial values are one. -/
def saddleBenchmark (n : ℕ) : ℝ :=
  if n < 2 then 1 else
    let r := halfDegree n
    let ρ := saddleRadius r
    ((Nat.factorial n : ℝ) * (binarySubspaceCount r : ℝ) *
      (1 + ρ / 6) ^ parity n * Real.exp (criticalPolynomial ρ)) /
      (ρ ^ r * Real.sqrt (2 * Real.pi * saddleVariance ρ))

/-- Index `k = 0` is the product's first factor, `1 - 2⁻¹`. -/
def eulerFactor (k : ℕ) : ℝ := 1 - (2 : ℝ) ^ (-((k : ℝ) + 1))

def eulerProduct : ℝ := ∏' k : ℕ, eulerFactor k

def thetaEvenTerm (j : ℤ) : ℝ := (2 : ℝ) ^ (-((j : ℝ) ^ 2))

def thetaOddTerm (j : ℤ) : ℝ := (2 : ℝ) ^ (-((j : ℝ) * ((j : ℝ) - 1)))

def kappaEven : ℝ := eulerProduct⁻¹ * ∑' j : ℤ, thetaEvenTerm j

def kappaOdd : ℝ := eulerProduct⁻¹ * ∑' j : ℤ, thetaOddTerm j

/-- The fixed, explicit, four-periodic main-term constants. -/
def residueConstant (j : ℕ) : ℝ :=
  match j % 4 with
  | 0 => Real.exp (-(4 / 3 : ℝ)) * kappaEven / (2 : ℝ) ^ (1 / 2 : ℝ)
  | 1 => Real.exp (-(4 / 3 : ℝ)) * kappaEven * (48 : ℝ) ^ (3 / 8 : ℝ) /
      (6 * (2 : ℝ) ^ (7 / 16 : ℝ))
  | 2 => Real.exp (-(4 / 3 : ℝ)) * kappaOdd / (2 : ℝ) ^ (3 / 4 : ℝ)
  | _ => Real.exp (-(4 / 3 : ℝ)) * kappaOdd * (48 : ℝ) ^ (3 / 8 : ℝ) /
      (6 * (2 : ℝ) ^ (11 / 16 : ℝ))

/-- The fully elementary main term `M_n`, with `M_0 = 1`.
The denominator `Real.exp 7` is the mathematical `e^7`. -/
def elementaryBenchmark (n : ℕ) : ℝ :=
  if n = 0 then 1 else
    residueConstant n *
      (n : ℝ) ^ ((3 : ℝ) * (parity n : ℝ) / 8) *
      (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16) *
      ((n : ℝ) ^ 7 / (48 * (2 : ℝ) ^ parity n * Real.exp 7)) ^ ((n : ℝ) / 8) *
      Real.exp (2 * Real.sqrt ((n : ℝ) / 3) +
        (48 * (n : ℝ)) ^ (1 / 4 : ℝ) / 2)

/-- Subtraction is in `ℝ`: the even correction is negative. -/
def firstCorrection (n : ℕ) : ℝ :=
  (6 * (parity n : ℝ) - 4) / (48 * (n : ℝ)) ^ (1 / 4 : ℝ)

/-- Semantic obligations, to be proved rather than accepted as assumptions.
The convergence fields exclude relying on default values of infinite sums
or products. The finite-cardinality fields identify actual finite counts. -/
structure DefinitionChecks : Prop where
  subgroup_finite : ∀ n : ℕ, Finite (Subgroup (Equiv.Perm (Fin n)))
  subspace_finite : ∀ r : ℕ, Finite (Submodule (ZMod 2) (Fin r → ZMod 2))
  exact_positive : ∀ n : ℕ, 0 < exactBenchmark n
  exact_zero : exactBenchmark 0 = 1
  exact_one : exactBenchmark 1 = 1
  saddle_positive_unique : ∀ r : ℕ, 0 < r →
    0 < saddleRadius r ∧ saddleMean (saddleRadius r) = (r : ℝ) ∧
      ∀ x : ℝ, 0 < x → saddleMean x = (r : ℝ) → x = saddleRadius r
  saddle_positive : ∀ n : ℕ, 0 < saddleBenchmark n
  euler_multipliable : Multipliable eulerFactor
  euler_positive : 0 < eulerProduct
  theta_even_summable : Summable thetaEvenTerm
  theta_odd_summable : Summable thetaOddTerm
  residue_positive : ∀ j : ℕ, 0 < residueConstant j
  elementary_positive : ∀ n : ℕ, 0 < elementaryBenchmark n

/-- T1: exponential relative error, uniform across both parities. -/
def T1 : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      |(subgroupCount n : ℝ) / exactBenchmark n - 1| ≤
        K * (2 : ℝ) ^ (-c * (n : ℝ))

/-- T2: relative `O(1/n)` error against the exact positive saddle. -/
def T2 : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      |(subgroupCount n : ℝ) / saddleBenchmark n - 1| ≤ K / (n : ℝ)

/-- T3: the explicit first correction, with uniform `O(n⁻¹ᐟ²)` remainder. -/
def T3 : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      |(subgroupCount n : ℝ) / elementaryBenchmark n - 1 - firstCorrection n| ≤
        K / Real.sqrt (n : ℝ)

/-- The requested targets together with their definition obligations.
Each target has constants uniform in `n`; the three thresholds may later be
replaced by their maximum to obtain the joint form in `SPEC.md`. -/
def AllTargets : Prop := DefinitionChecks ∧ T1 ∧ T2 ∧ T3

end SymmetricSubgroupAsymptotics
