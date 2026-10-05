import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairQuotientPackage
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailDecay

/-!
# Quadratic growth retained before affine prepending

The correlated pair rows are first proved before physical pointing.  Their
exceptional term is therefore not itself small: it has the main
`2^(b^2/16)` subgroup-count growth, with a fixed quadratic deficit.  This
file records exactly that pre-pointing statement.  A later affine layer may
add any fixed linear exponential cost and then apply the physical pointing
factor at its actual ambient width.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A raw exceptional term has the universal subgroup-count quadratic term
with a strictly smaller quadratic coefficient.  Constants and all linear
costs may be absorbed after a fixed affine layer is prepended. -/
structure RawQuadraticExceptionalBound (X : ℕ → ℝ) where
  threshold : ℕ
  rate : ℝ
  constant : ℝ
  rate_pos : 0 < rate
  constant_pos : 0 < constant
  bound : ∀ b, threshold ≤ b →
    X b ≤ constant *
      (2 : ℝ) ^ (((1 / 16 : ℝ) - rate) * (b : ℝ) ^ 2)

/-- The raw quotient package together with the growth certificate which is
needed after another elementary affine layer is prepended. -/
structure PreE7DegreeTwoPairQuotientGrowthPackage
    (Q : Type) [Group Q] [Finite Q] : Type 1 where
  package : PreE7DegreeTwoPairQuotientSummedPackage Q
  exceptionalGrowth :
    FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)) →
      RawQuadraticExceptionalBound package.envelope.exceptionalRaw

namespace PreE7DegreeTwoPairQuotientGrowthPackage

/-- Literal-target transport does not alter the exceptional function. -/
noncomputable def comapEquiv
    {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']
    (e : Q ≃* Q')
    (S : PreE7DegreeTwoPairQuotientGrowthPackage Q') :
    PreE7DegreeTwoPairQuotientGrowthPackage Q where
  package := S.package.comapEquiv e
  exceptionalGrowth := S.exceptionalGrowth

/-- A row whose raw exceptional term vanishes has arbitrary positive
quadratic reserve. -/
noncomputable def ofZero
    {Q : Type} [Group Q] [Finite Q]
    (S : PreE7DegreeTwoPairQuotientSummedPackage Q)
    (hzero : S.envelope.exceptionalRaw = fun _ => 0) :
    PreE7DegreeTwoPairQuotientGrowthPackage Q where
  package := S
  exceptionalGrowth := fun _ => by
    refine
      { threshold := 0
        rate := 1 / 100000
        constant := 1
        rate_pos := by norm_num
        constant_pos := by norm_num
        bound := ?_ }
    intro b _
    rw [hzero]
    exact mul_nonneg zero_le_one (by positivity)

end PreE7DegreeTwoPairQuotientGrowthPackage

/-! ## The common `51/200` raw tail -/

/-- The raw exceptional function common to Y1 and the two central-product
rows, with the finite row coefficient left explicit. -/
def rankTail51RawExceptional (K : ℝ) (b : ℕ) : ℝ :=
  K * ((Nat.factorial b : ℕ) : ℝ) ^ 17 *
    ((2 : ℝ) ^
        (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
      (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))

theorem rankTail51RawExceptional_nonneg
    {K : ℝ} (hK : 0 ≤ K) (b : ℕ) :
    0 ≤ rankTail51RawExceptional K b := by
  unfold rankTail51RawExceptional
  have hs : (0 : ℝ) ≤ subgroupCount (b + 2 * rankTail51Tilt b) := by
    exact_mod_cast (subgroupCount_pos _).le
  positivity

private theorem rankTail51_degree_le_three_mul (b : ℕ) (hb : 1 ≤ b) :
    b + 2 * rankTail51Tilt b ≤ 3 * b := by
  unfold rankTail51Tilt
  omega

/-- The complete-source coarse estimate and the proved rank-tail square
completion give a reusable raw quadratic deficit.  Physical pointing is
deliberately absent from this statement. -/
theorem rankTail51RawExceptional_eventually
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    {K : ℝ} (hK : 0 ≤ K) :
    ∀ᶠ b : ℕ in atTop,
      rankTail51RawExceptional K b ≤
        (K * (2 : ℝ) ^ (1 / 4 : ℝ)) *
          (2 : ℝ) ^
            (((1 / 16 : ℝ) - 1 / 50000) * (b : ℝ) ^ 2) := by
  let epsilon : ℝ := 1 / 10000000
  let gamma : ℝ := 1 / 10000000
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hgamma : 0 < gamma := by norm_num [gamma]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcoarse epsilon hepsilon)
  filter_upwards [eventually_ge_atTop (max N 1),
    eventually_succ_le_two_rpow hgamma] with b hb hsucc
  let q : ℕ := rankTail51Tilt b
  let M : ℕ := b + 2 * q
  have hbN : N ≤ b := (le_max_left _ _).trans hb
  have hb1 : 1 ≤ b := (le_max_right _ _).trans hb
  have hbM : b ≤ M := Nat.le_add_right _ _
  have hMN : N ≤ M := hbN.trans hbM
  have hM3 : M ≤ 3 * b := by
    simpa only [M, q] using rankTail51_degree_le_three_mul b hb1
  have hM3R : (M : ℝ) ≤ 3 * (b : ℝ) := by exact_mod_cast hM3
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hM2 : (M : ℝ) ^ 2 ≤ 9 * (b : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (3 * (b : ℝ) - M)]
  have hs := hN M hMN
  have hfacNat := factorial_le_succ_pow b
  have hfac : ((b.factorial : ℕ) : ℝ) ^ 17 ≤
      (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) := by
    have hfacR : ((b.factorial : ℕ) : ℝ) ≤
        (((b + 1 : ℕ) : ℝ) ^ b) := by exact_mod_cast hfacNat
    have hpow := pow_le_pow_left₀ (by positivity) hfacR 17
    have hsuccpow := pow_le_pow_left₀ (by positivity) hsucc (17 * b)
    calc
      ((b.factorial : ℕ) : ℝ) ^ 17 ≤
          ((((b + 1 : ℕ) : ℝ) ^ b) ^ 17) := hpow
      _ = (((b + 1 : ℕ) : ℝ) ^ (17 * b)) := by ring
      _ ≤ (((2 : ℝ) ^ (gamma * b)) ^ (17 * b)) := hsuccpow
      _ = (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        push_cast
        ring
  have hsquare := y1RankTail_squareCompletion b
  have hexponent :
      17 * gamma * (b : ℝ) ^ 2 +
          (-((q : ℝ) * (51 / 200) * b)) +
          (1 / 16 + epsilon) * (M : ℝ) ^ 2 ≤
        ((1 / 16 : ℝ) - 1 / 50000) * (b : ℝ) ^ 2 + 1 / 4 := by
    have heM : epsilon * (M : ℝ) ^ 2 ≤
        9 * epsilon * (b : ℝ) ^ 2 := by
      calc
        _ ≤ epsilon * (9 * (b : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hM2 hepsilon.le
        _ = _ := by ring
    have hsquare' :
        (M : ℝ) ^ 2 / 16 - (q : ℝ) * (51 / 200) * b ≤
          (b : ℝ) ^ 2 / 16 - (b : ℝ) ^ 2 / 40000 + 1 / 4 := by
      simpa only [M, q, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        hsquare
    dsimp [epsilon, gamma] at heM ⊢
    push_cast at hsquare' ⊢
    nlinarith
  have hsource : rankTail51RawExceptional K b ≤
      K * (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) *
        ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
          (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) := by
    unfold rankTail51RawExceptional
    dsimp only [q, M] at hs
    calc
      K * ((Nat.factorial b : ℕ) : ℝ) ^ 17 *
          ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
            (subgroupCount M : ℝ)) ≤
          K * ((Nat.factorial b : ℕ) : ℝ) ^ 17 *
            ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
              (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs (by positivity))
          (mul_nonneg hK (by positivity))
      _ ≤ K * (2 : ℝ) ^ (17 * gamma * (b : ℝ) ^ 2) *
            ((2 : ℝ) ^ (-((q : ℝ) * (51 / 200) * b)) *
              (2 : ℝ) ^ ((1 / 16 + epsilon) * (M : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfac hK) (by positivity)
  calc
    rankTail51RawExceptional K b ≤ _ := hsource
    _ = K * (2 : ℝ) ^
        (17 * gamma * (b : ℝ) ^ 2 +
          (-((q : ℝ) * (51 / 200) * b)) +
          (1 / 16 + epsilon) * (M : ℝ) ^ 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [mul_assoc]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ K * (2 : ℝ) ^
        (((1 / 16 : ℝ) - 1 / 50000) * (b : ℝ) ^ 2 + 1 / 4) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hK
    _ = (K * (2 : ℝ) ^ (1 / 4 : ℝ)) *
        (2 : ℝ) ^
          (((1 / 16 : ℝ) - 1 / 50000) * (b : ℝ) ^ 2) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring

/-- Package the preceding eventual inequality in a form with a strictly
positive constant, including the zero-coefficient case. -/
noncomputable def rankTail51RawExceptional_bound
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    {K : ℝ} (hK : 0 ≤ K) :
    RawQuadraticExceptionalBound (rankTail51RawExceptional K) := by
  let h := eventually_atTop.mp
    (rankTail51RawExceptional_eventually hcoarse hK)
  let N : ℕ := Classical.choose h
  have hN := Classical.choose_spec h
  let C : ℝ := K * (2 : ℝ) ^ (1 / 4 : ℝ)
  refine
    { threshold := N
      rate := 1 / 50000
      constant := C + 1
      rate_pos := by norm_num
      constant_pos := by
        have hC : 0 ≤ C := by
          dsimp [C]
          positivity
        linarith
      bound := ?_ }
  intro b hb
  have hraw := hN b hb
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  exact hraw.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
