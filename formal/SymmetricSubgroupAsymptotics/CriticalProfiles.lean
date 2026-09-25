import SymmetricSubgroupAsymptotics.GeneratingFunction
import Mathlib.Data.Nat.Choose.Cast

/-!
# Four-colour critical profiles

A profile records separate multiplicities for the C₂, V₄, D₈ and E₈
colours. This module proves their finite weighted-sum identity. It does not
identify profiles, or their rational weights, with actual permutation
subgroups; that correspondence is a separate group-theoretic statement.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

/-- The four independent nonnegative multiplicities of a critical profile. -/
structure CriticalProfile where
  c2 : ℕ
  v4 : ℕ
  d8 : ℕ
  e8 : ℕ
  deriving DecidableEq

/-- Half of the total support size of a four-colour profile. -/
def CriticalProfile.rank (p : CriticalProfile) : ℕ :=
  p.c2 + 2 * p.v4 + 2 * p.d8 + 4 * p.e8

/-- The rational profile weight, retaining the two distinct rank-two colours. -/
def CriticalProfile.weight (p : CriticalProfile) : ℚ :=
  1 / ((2 : ℚ) ^ p.c2 * (Nat.factorial p.c2 : ℚ) *
    24 ^ p.v4 * (Nat.factorial p.v4 : ℚ) *
    8 ^ p.d8 * (Nat.factorial p.d8 : ℚ) *
    384 ^ p.e8 * (Nat.factorial p.e8 : ℚ))

private abbrev ProfileIndex := (_ : (ℕ × ℕ) × ℕ) × ℕ

private def profileIndices (r : ℕ) : Finset ProfileIndex :=
  (((Finset.range (r + 1)).product (Finset.range (r + 1))).product
    (Finset.range (r + 1))).sigma (fun q => Finset.range (q.1.2 + 1))

private def profileOfIndex (i : ProfileIndex) : CriticalProfile :=
  ⟨i.1.1.1, i.2, i.1.1.2 - i.2, i.1.2⟩

/-- The finite set of all four-colour profiles of rank `r`. The triangular
index only enumerates the split `v4 + d8`; it imposes no extra restriction. -/
def criticalProfiles (r : ℕ) : Finset CriticalProfile :=
  ((profileIndices r).image profileOfIndex).filter (fun p => p.rank = r)

private theorem mem_profileIndices (r : ℕ) (i : ProfileIndex) :
    i ∈ profileIndices r ↔
      i.1.1.1 ≤ r ∧ i.1.1.2 ≤ r ∧ i.1.2 ≤ r ∧ i.2 ≤ i.1.1.2 := by
  simp [profileIndices]
  omega

private theorem profileOfIndex_injective (r : ℕ) :
    Set.InjOn profileOfIndex (profileIndices r : Set ProfileIndex) := by
  intro i hi j hj hij
  have hi' := (mem_profileIndices r i).mp hi
  have hj' := (mem_profileIndices r j).mp hj
  have ha := congrArg CriticalProfile.c2 hij
  have hv := congrArg CriticalProfile.v4 hij
  have hb := congrArg CriticalProfile.d8 hij
  have he := congrArg CriticalProfile.e8 hij
  dsimp [profileOfIndex] at ha hv hb he
  have hk : i.1.1.2 = j.1.1.2 := by omega
  exact Sigma.ext (Prod.ext (Prod.ext ha hk) he) (by simpa using hv)

/-- Membership is exactly the stated weighted-rank constraint. In particular,
every quadruple satisfying it occurs once in the finite profile set. -/
@[simp] theorem mem_criticalProfiles (r : ℕ) (p : CriticalProfile) :
    p ∈ criticalProfiles r ↔ p.rank = r := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hp⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨((p.c2, p.v4 + p.d8), p.e8), p.v4⟩, ?_, ?_⟩
    · rw [mem_profileIndices]
      dsimp
      unfold CriticalProfile.rank at hp
      omega
    · cases p
      simp [profileOfIndex]

/-- The sum is over actual four-coordinate profiles, each with its own weight. -/
def criticalProfileSum (r : ℕ) : ℚ :=
  ∑ p ∈ criticalProfiles r, p.weight

/-- The ordinary exponential binomial convolution, before inserting weights. -/
theorem factorial_binomial_convolution (x y : ℚ) (k : ℕ) :
    (∑ v ∈ Finset.range (k + 1),
      x ^ v / (Nat.factorial v : ℚ) *
        (y ^ (k - v) / (Nat.factorial (k - v) : ℚ))) =
      (x + y) ^ k / (Nat.factorial k : ℚ) := by
  rw [add_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  have hvk : v ≤ k := by simpa using Finset.mem_range.mp hv
  rw [Nat.cast_choose ℚ hvk]
  have hk : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have hv' : (Nat.factorial v : ℚ) ≠ 0 := by positivity
  have hkv : (Nat.factorial (k - v) : ℚ) ≠ 0 := by positivity
  field_simp

/-- The V₄ and D₈ colours combine by `1/24 + 1/8 = 1/6`, including `k = 0`. -/
theorem rankTwo_profile_convolution (k : ℕ) :
    (∑ v ∈ Finset.range (k + 1),
      1 / ((24 : ℚ) ^ v * (Nat.factorial v : ℚ) *
        8 ^ (k - v) * (Nat.factorial (k - v) : ℚ))) =
      1 / ((6 : ℚ) ^ k * (Nat.factorial k : ℚ)) := by
  have h := factorial_binomial_convolution (1 / 24) (1 / 8) k
  norm_num at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro v hv
    simp only [div_pow, one_pow]
    ring
  · simp only [div_pow, one_pow]
    ring

/-- Summing the two rank-two colours in a fixed outer profile recovers
its rank-two aggregate weight. -/
theorem profileWeight_split_sum (a k e : ℕ) :
    (∑ v ∈ Finset.range (k + 1),
      CriticalProfile.weight ⟨a, v, k - v, e⟩) =
      1 / ((2 : ℚ) ^ a * (Nat.factorial a : ℚ) *
        6 ^ k * (Nat.factorial k : ℚ) * 384 ^ e * (Nat.factorial e : ℚ)) := by
  calc
    _ = (1 / ((2 : ℚ) ^ a * (Nat.factorial a : ℚ) *
          384 ^ e * (Nat.factorial e : ℚ))) *
        ∑ v ∈ Finset.range (k + 1),
          1 / ((24 : ℚ) ^ v * (Nat.factorial v : ℚ) *
            8 ^ (k - v) * (Nat.factorial (k - v) : ℚ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [CriticalProfile.weight, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [rankTwo_profile_convolution]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Exact four-colour weighted profile identity. Enumeration is injective,
and membership is exactly the rank constraint, rather than a definition of
an unspecified family count. -/
theorem criticalProfileSum_eq_criticalCoefficient (r : ℕ) :
    criticalProfileSum r = criticalCoefficient r := by
  unfold criticalProfileSum criticalProfiles
  rw [Finset.sum_filter, Finset.sum_image (profileOfIndex_injective r)]
  unfold profileIndices
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_sigma, Finset.sum_product]
  simp_rw [Finset.sum_product]
  unfold criticalCoefficient
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro e he
  calc
    _ = ∑ v ∈ Finset.range (k + 1),
        if a + 2 * k + 4 * e = r then
          CriticalProfile.weight ⟨a, v, k - v, e⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvk : v ≤ k := by simpa using Finset.mem_range.mp hv
      have hrank : CriticalProfile.rank ⟨a, v, k - v, e⟩ = a + 2 * k + 4 * e := by
        dsimp [CriticalProfile.rank]
        omega
      simp only [profileOfIndex, hrank]
    _ = _ := by
      rw [Finset.sum_ite_irrel, profileWeight_split_sum]
      simp

/-- The optional rank-one parity decoration has weight `1/6`. The explicit
positive-rank guard prevents a spurious decorated rank-zero profile. -/
def parityCriticalProfileSum (n : ℕ) : ℚ :=
  criticalProfileSum (halfDegree n) +
    if parity n = 1 ∧ 0 < halfDegree n then
      criticalProfileSum (halfDegree n - 1) / 6 else 0

/-- Exact parity-adjusted profile identity, including degrees zero and one. -/
theorem parityCriticalProfileSum_eq_parityCoefficient (n : ℕ) :
    parityCriticalProfileSum n = parityCoefficient n := by
  simp only [parityCriticalProfileSum, parityCoefficient,
    criticalProfileSum_eq_criticalCoefficient]

end SymmetricSubgroupAsymptotics
