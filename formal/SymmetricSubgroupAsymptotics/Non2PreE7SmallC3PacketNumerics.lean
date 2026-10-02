import SymmetricSubgroupAsymptotics.Non2PreE7SmallC3PacketCounting
import SymmetricSubgroupAsymptotics.FusionWidthUniformNormalization
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailDecay
import SymmetricSubgroupAsymptotics.ForwardEstimateAlgebra
import SymmetricSubgroupAsymptotics.C1LowCone

/-!
# Numerical closure of the complete degree-three packet

Positive retained tails give an honest forward row at their literal tail
degree.  Empty tails give a scalar.  Both estimates keep the simultaneous
number `c` of regular `C3` orbits, which supplies the missing aggregate
deficit that no pointwise width-three action can have.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedC3TailPhysical RepeatedC3TailExtraction

/-- The local positive-tail factor after exact benchmark cancellation.  The
normalizer and occurrence factorials have only been discarded downward. -/
def preE7SmallC3PositiveCoefficient {n : ℕ}
    (p : RepeatedC3PositiveProfileIndex n) : ℝ :=
  fusionWidthPointingRatio (p.m : ℕ) (3 * (p.c : ℕ)) *
    (((p.c : ℕ) + 1 : ℕ) : ℝ) *
      (3 : ℝ) ^ ((p.c : ℕ) * p.c / 4 + p.c +
        (3 * (p.m : ℕ) / 20) * p.c)

/-- The packet's forward row, grouped by the literal retained-tail degree. -/
def preE7SmallC3PositiveKernel (n m : ℕ) : ℝ :=
  ∑ p : RepeatedC3PositiveProfileIndex n,
    if (p.m : ℕ) = m then preE7SmallC3PositiveCoefficient p else 0

/-- The benchmark-normalized empty-tail upper bound. -/
def preE7SmallC3PureScalar (n : ℕ) : ℝ :=
  ∑ p : RepeatedC3PureProfileIndex n,
    ((n.factorial : ℝ) *
      ((((p.c : ℕ) + 1 : ℕ) : ℝ) *
        (3 : ℝ) ^ ((p.c : ℕ) * p.c / 4 + p.c))) /
        exactBenchmark n

/-- Exact normalized size of the complete degree-three packet. -/
def preE7SmallC3PacketRatio (n : ℕ) : ℝ :=
  Nat.card (PreE7SmallC3PacketSubgroupSet n) / exactBenchmark n

private def positiveChart {n : ℕ}
    (p : RepeatedC3PositiveProfileIndex n) :
    RepeatedC3TailProfile.ModelPoints p.c p.m ≃ Fin n :=
  orbitProfileFinLabels (RepeatedC3TailProfile.points p.m)
    (RepeatedC3TailProfile.multiplicity p.c) n (by
      have hcard : Fintype.card TernaryCyclic = 3 := by
        norm_num [TernaryCyclic]
      simp only [Fintype.sum_sum_type, Fintype.sum_unique]
      change (p.c : ℕ) * Fintype.card TernaryCyclic +
        1 * Fintype.card (Fin (p.m : ℕ)) = n
      rw [hcard, Fintype.card_fin]
      simpa [Nat.mul_comm] using p.degree_eq)

private def pureChart {n : ℕ}
    (p : RepeatedC3PureProfileIndex n) :
    RepeatedC3PureProfile.ModelPoints p.c ≃ Fin n :=
  orbitProfileFinLabels RepeatedC3PureProfile.points
    (RepeatedC3PureProfile.multiplicity p.c) n (by
      simp only [Fintype.sum_unique]
      change (p.c : ℕ) * Fintype.card TernaryCyclic = n
      norm_num [TernaryCyclic]
      simpa [Nat.mul_comm] using p.degree_eq)

private theorem positiveProfile_normalized_le {n : ℕ}
    (p : RepeatedC3PositiveProfileIndex n) :
    (Nat.card (AssembledOrbitProfileOn
        (RepeatedC3TailProfile.modelPredicate p.c
          (3 * p.m / 20) p.m) (Fin n)) : ℝ) /
        exactBenchmark n ≤
      preE7SmallC3PositiveCoefficient p * ordinarySubgroupRatio p.m := by
  have hcount := RepeatedC3TailProfile.assembled_card_le p.c
    (3 * p.m / 20) p.m p.m_pos (positiveChart p)
  have hden : (1 : ℝ) ≤
      (6 : ℝ) ^ (p.c : ℕ) * ((p.c : ℕ).factorial : ℝ) := by
    have hpow : (1 : ℝ) ≤ (6 : ℝ) ^ (p.c : ℕ) :=
      one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ ((p.c : ℕ).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (p.c : ℕ))
    nlinarith [mul_le_mul hpow hfac (by norm_num) (by positivity)]
  have hdrop :
      ((((3 * (p.c : ℕ) + p.m).factorial : ℝ) *
          ((subgroupCount p.m : ℝ) *
            (((p.c : ℕ) + 1) *
              3 ^ ((p.c : ℕ) * p.c / 4 + p.c +
                (3 * (p.m : ℕ) / 20) * p.c)))) /
        (((6 : ℝ) ^ (p.c : ℕ) * ((p.c : ℕ).factorial : ℝ)) *
          ((p.m : ℕ).factorial : ℝ)) ≤
      (((3 * (p.c : ℕ) + p.m).factorial : ℝ) *
          ((subgroupCount p.m : ℝ) *
            (((p.c : ℕ) + 1) *
              3 ^ ((p.c : ℕ) * p.c / 4 + p.c +
                (3 * (p.m : ℕ) / 20) * p.c)))) /
        ((p.m : ℕ).factorial : ℝ)) := by
    have hnum : 0 ≤
        (((3 * (p.c : ℕ) + p.m).factorial : ℝ) *
          ((subgroupCount p.m : ℝ) *
            (((p.c : ℕ) + 1) *
              3 ^ ((p.c : ℕ) * p.c / 4 + p.c +
                (3 * (p.m : ℕ) / 20) * p.c)))) := by positivity
    have hmfac : 0 < (((p.m : ℕ).factorial : ℝ)) := by positivity
    apply div_le_div_of_nonneg_left hnum hmfac
    calc
      ((p.m : ℕ).factorial : ℝ) =
          1 * ((p.m : ℕ).factorial : ℝ) := by ring
      _ ≤ ((6 : ℝ) ^ (p.c : ℕ) * ((p.c : ℕ).factorial : ℝ)) *
          ((p.m : ℕ).factorial : ℝ) :=
        mul_le_mul_of_nonneg_right hden (by positivity)
  have hn : 3 * (p.c : ℕ) + p.m = n := p.degree_eq
  have hn' : (p.m : ℕ) + 3 * p.c = n := by omega
  have hbench := exactBenchmark_pos n
  norm_num only [Nat.cast_add, Nat.cast_one] at hcount hdrop ⊢
  apply (div_le_div_of_nonneg_right (hcount.trans hdrop) hbench.le).trans_eq
  unfold preE7SmallC3PositiveCoefficient ordinarySubgroupRatio
    fusionWidthPointingRatio
  rw [hn, hn']
  field_simp [ne_of_gt (exactBenchmark_pos (p.m : ℕ)),
    ne_of_gt (exactBenchmark_pos n)]
  push_cast
  ring

private theorem pureProfile_normalized_le {n : ℕ}
    (p : RepeatedC3PureProfileIndex n) :
    (Nat.card (AssembledOrbitProfileOn
        (RepeatedC3PureProfile.modelPredicate p.c) (Fin n)) : ℝ) /
        exactBenchmark n ≤
      ((n.factorial : ℝ) *
        (((p.c : ℕ) + 1) * 3 ^ ((p.c : ℕ) * p.c / 4 + p.c))) /
          exactBenchmark n := by
  have h := RepeatedC3PureProfile.assembled_card_le p.c (pureChart p)
  rw [p.degree_eq] at h
  push_cast at h ⊢
  exact div_le_div_of_nonneg_right h (exactBenchmark_pos n).le

theorem preE7SmallC3PacketRatio_recurrence
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) :
    preE7SmallC3PacketRatio n ≤ preE7SmallC3PureScalar n +
      ∑ m ∈ Finset.range n,
        preE7SmallC3PositiveKernel n m * ordinarySubgroupRatio m := by
  have hpure := preE7SmallC3PacketPure_card_le n
  have hpos := preE7SmallC3PacketPositive_card_le
    hChief hWeight hPrimitive h18 n
  have hsplit := preE7SmallC3Packet_card_eq n
  have hcard : (Nat.card (PreE7SmallC3PacketSubgroupSet n) : ℝ) ≤
      (∑ p : RepeatedC3PureProfileIndex n,
        Nat.card (AssembledOrbitProfileOn
          (RepeatedC3PureProfile.modelPredicate p.c) (Fin n))) +
      ∑ p : RepeatedC3PositiveProfileIndex n,
        Nat.card (AssembledOrbitProfileOn
          (RepeatedC3TailProfile.modelPredicate p.c
            (3 * p.m / 20) p.m) (Fin n)) := by
    exact_mod_cast (show Nat.card (PreE7SmallC3PacketSubgroupSet n) ≤ _ by
      rw [hsplit]
      exact Nat.add_le_add hpure hpos)
  have hbench := exactBenchmark_pos n
  apply (div_le_div_of_nonneg_right hcard hbench.le).trans
  rw [add_div]
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  have hpure' :
      (∑ p : RepeatedC3PureProfileIndex n,
        (Nat.card (AssembledOrbitProfileOn
          (RepeatedC3PureProfile.modelPredicate p.c) (Fin n)) : ℝ) /
            exactBenchmark n) ≤ preE7SmallC3PureScalar n := by
    unfold preE7SmallC3PureScalar
    exact Finset.sum_le_sum (fun p _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using pureProfile_normalized_le p)
  have hpos' :
      (∑ p : RepeatedC3PositiveProfileIndex n,
        (Nat.card (AssembledOrbitProfileOn
          (RepeatedC3TailProfile.modelPredicate p.c
            (3 * p.m / 20) p.m) (Fin n)) : ℝ) /
              exactBenchmark n) ≤
        ∑ m ∈ Finset.range n,
          preE7SmallC3PositiveKernel n m * ordinarySubgroupRatio m := by
    calc
      _ ≤ ∑ p : RepeatedC3PositiveProfileIndex n,
          preE7SmallC3PositiveCoefficient p * ordinarySubgroupRatio p.m :=
        Finset.sum_le_sum (fun p _ => positiveProfile_normalized_le p)
      _ = _ := by
        unfold preE7SmallC3PositiveKernel
        symm
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        have hpm : (p.m : ℕ) < n := by
          have hc : 0 < (p.c : ℕ) := p.c_pos
          have hn := p.degree_eq
          omega
        simp [hpm]
  exact add_le_add hpure' hpos'

theorem preE7SmallC3PositiveKernel_nonneg (n m : ℕ) :
    0 ≤ preE7SmallC3PositiveKernel n m := by
  unfold preE7SmallC3PositiveKernel preE7SmallC3PositiveCoefficient
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact mul_nonneg
      (mul_nonneg (fusionWidthPointingRatio_nonneg _ _) (by positivity))
      (by positivity)
  · exact le_rfl

private theorem positiveLocalFactor_le (c m : ℕ) :
    (((c + 1 : ℕ) : ℝ) *
        (3 : ℝ) ^ (c * c / 4 + c + (3 * m / 20) * c)) ≤
      (((c + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (((8 : ℝ) / 5) * ((c * c / 4 : ℕ) + c) +
          (6 : ℝ) / 25 * m * c)) := by
  let a := c * c / 4 + c
  let d := 3 * m / 20
  have hd : 20 * d ≤ 3 * m := by
    dsimp [d]
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (3 * m) 20
  have ha :
      (3 : ℝ) ^ a ≤ (2 : ℝ) ^ (((8 : ℝ) / 5) * a) := by
    calc
      _ ≤ ((2 : ℝ) ^ ((8 : ℝ) / 5)) ^ a :=
        pow_le_pow_left₀ (by norm_num) c1_three_le_binary_envelope a
      _ = _ := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hd0 := c1_low_power_le m d hd
  have hdc : ((3 : ℝ) ^ d) ^ c ≤
      ((2 : ℝ) ^ ((6 : ℝ) / 25 * m)) ^ c :=
    pow_le_pow_left₀ (by positivity) hd0 c
  have hdc' : (3 : ℝ) ^ (d * c) ≤
      (2 : ℝ) ^ ((6 : ℝ) / 25 * m * c) := by
    calc
      _ = ((3 : ℝ) ^ d) ^ c := by rw [pow_mul]
      _ ≤ ((2 : ℝ) ^ ((6 : ℝ) / 25 * m)) ^ c := hdc
      _ = _ := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hprod := mul_le_mul ha hdc' (by positivity) (by positivity)
  have hpow :
      (3 : ℝ) ^ (a + d * c) ≤
        (2 : ℝ) ^ (((8 : ℝ) / 5) * a + (6 : ℝ) / 25 * m * c) := by
    calc
      _ = (3 : ℝ) ^ a * (3 : ℝ) ^ (d * c) := by rw [pow_add]
      _ ≤ (2 : ℝ) ^ (((8 : ℝ) / 5) * a) *
          (2 : ℝ) ^ ((6 : ℝ) / 25 * m * c) := hprod
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  dsimp [a, d] at hpow
  push_cast at hpow
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The simultaneous number of regular triples pays for its own local
ternary freedom, uniformly in the retained-tail degree. -/
private theorem positiveExponent_le (c m : ℕ) (hc : 0 < c) :
    -(halfDegree (3 * c) : ℝ) * m / 4 -
          (halfDegree (3 * c) : ℝ) ^ 2 / 4 +
          (halfDegree (3 * c) : ℝ) / 4 + 1 / 4 +
          (8 : ℝ) / 5 * ((c * c / 4 : ℕ) + c) +
          (6 : ℝ) / 25 * m * c ≤
      11 - (c : ℝ) * (m + 3 * c) / 100 := by
  let r := halfDegree (3 * c)
  have hlo : 3 * c ≤ 2 * r + 1 := by
    dsimp [r, halfDegree]
    omega
  have hhi : 2 * r ≤ 3 * c := by
    dsimp [r, halfDegree]
    omega
  have hdivNat : (c * c / 4) * 4 ≤ c * c :=
    Nat.div_mul_le_self (c * c) 4
  have hloR : (3 : ℝ) * c ≤ 2 * r + 1 := by exact_mod_cast hlo
  have hhiR : (2 : ℝ) * r ≤ 3 * c := by exact_mod_cast hhi
  have hdivR : ((c * c / 4 : ℕ) : ℝ) * 4 ≤ (c : ℝ) ^ 2 := by
    have hdivR' : ((c * c / 4 : ℕ) : ℝ) * 4 ≤
        (c : ℝ) * c := by exact_mod_cast hdivNat
    simpa only [pow_two] using hdivR'
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hrR : (0 : ℝ) ≤ r := by positivity
  have hcm : 0 ≤ ((c : ℝ) - 1) * m :=
    mul_nonneg (by linarith) hmR
  have hrm : 0 ≤ (2 * (r : ℝ) + 1 - 3 * c) * m :=
    mul_nonneg (by linarith) hmR
  have hrsq : 0 ≤
      (2 * (r : ℝ) + 1 - 3 * c) *
        (2 * r + 3 * c - 1) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hsquare : 0 ≤ (53 * (c : ℝ) - 470) ^ 2 := sq_nonneg _
  nlinarith

private theorem positiveCoefficient_le {n : ℕ}
    (p : RepeatedC3PositiveProfileIndex n) :
    preE7SmallC3PositiveCoefficient p ≤
      eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (3 * (p.c : ℕ) + 3)) *
        (2 : ℝ) ^ (11 - (p.c : ℝ) * n / 100) := by
  let c := (p.c : ℕ)
  let m := (p.m : ℕ)
  let r := halfDegree (3 * c)
  let L : ℝ := (8 : ℝ) / 5 * ((c * c / 4 : ℕ) + c) +
    (6 : ℝ) / 25 * m * c
  let E : ℝ := -(r : ℝ) * m / 4 - (r : ℝ) ^ 2 / 4 +
    (r : ℝ) / 4 + 1 / 4
  have hn : m + 3 * c = n := by
    dsimp [c, m]
    simpa [Nat.add_comm] using p.degree_eq
  have hc : 0 < c := p.c_pos
  have hpoint := fusionWidthPointingRatio_quadratic_le m (3 * c)
  have hlocal := positiveLocalFactor_le c m
  have hraw := mul_le_mul hpoint hlocal (by positivity)
    (by positivity [euler_positive])
  have hpoly :
      (((n + 1 : ℕ) : ℝ) ^ (3 * c + 2)) * ((c + 1 : ℕ) : ℝ) ≤
        (((n + 1 : ℕ) : ℝ) ^ (3 * c + 3)) := by
    have hcn : c + 1 ≤ n + 1 := by omega
    have hcnR : ((c + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcn
    calc
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (3 * c + 2)) *
          ((n + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcnR (by positivity)
      _ = _ := by rw [← pow_succ]
  have hexp : E + L ≤ 11 - (c : ℝ) * n / 100 := by
    have h := positiveExponent_le c m hc
    rw [← hn]
    push_cast
    simpa only [E, L, r, add_assoc] using h
  have hpow : (2 : ℝ) ^ (E + L) ≤
      (2 : ℝ) ^ (11 - (c : ℝ) * n / 100) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  unfold preE7SmallC3PositiveCoefficient
  rw [mul_assoc]
  change fusionWidthPointingRatio m (3 * c) *
      (((c + 1 : ℕ) : ℝ) *
        (3 : ℝ) ^ (c * c / 4 + c + (3 * m / 20) * c)) ≤
    eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (3 * c + 3)) *
      (2 : ℝ) ^ (11 - (c : ℝ) * n / 100)
  apply hraw.trans
  rw [hn]
  change
    (eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (3 * c + 2)) *
        (2 : ℝ) ^ E) *
      (((c + 1 : ℕ) : ℝ) * (2 : ℝ) ^ L) ≤ _
  have hmerge : (2 : ℝ) ^ E * (2 : ℝ) ^ L =
      (2 : ℝ) ^ (E + L) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 2) E L).symm
  calc
    _ = (eulerProduct⁻¹ ^ 2 *
          ((((n + 1 : ℕ) : ℝ) ^ (3 * c + 2)) * ((c + 1 : ℕ) : ℝ))) *
        ((2 : ℝ) ^ E * (2 : ℝ) ^ L) := by ac_rfl
    _ = (eulerProduct⁻¹ ^ 2 *
          ((((n + 1 : ℕ) : ℝ) ^ (3 * c + 2)) * ((c + 1 : ℕ) : ℝ))) *
        (2 : ℝ) ^ (E + L) := by
      rw [hmerge]
    _ ≤ (eulerProduct⁻¹ ^ 2 *
          (((n + 1 : ℕ) : ℝ) ^ (3 * c + 3))) *
        (2 : ℝ) ^ (11 - (c : ℝ) * n / 100) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hpoly (by positivity [euler_positive]))
        hpow (by positivity) (by positivity [euler_positive])
    _ = _ := by rfl

private theorem positiveCoefficient_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ p : RepeatedC3PositiveProfileIndex n,
      preE7SmallC3PositiveCoefficient p ≤
        (eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ 11) *
          (2 : ℝ) ^ (-(1 / 250 : ℝ) * n) := by
  let gamma : ℝ := 1 / 1000
  have hgamma : 0 < gamma := by norm_num [gamma]
  filter_upwards [eventually_succ_le_two_rpow hgamma] with n hsucc
  intro p
  let c := (p.c : ℕ)
  have hc : 0 < c := p.c_pos
  have hk : 3 * c + 3 ≤ 6 * c := by omega
  have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ (gamma * n) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hpoly0 := pow_le_pow_left₀ (by positivity) hsucc (3 * c + 3)
  have hpoly : (((n + 1 : ℕ) : ℝ) ^ (3 * c + 3)) ≤
      (2 : ℝ) ^ ((6 : ℝ) * gamma * c * n) := by
    calc
      _ ≤ ((2 : ℝ) ^ (gamma * n)) ^ (3 * c + 3) := hpoly0
      _ ≤ ((2 : ℝ) ^ (gamma * n)) ^ (6 * c) :=
        pow_le_pow_right₀ hbase hk
      _ = (2 : ℝ) ^ ((gamma * n) * (6 * c : ℕ)) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = _ := by
        push_cast
        congr 1 <;> ring
  have hmain :
      ((2 : ℝ) ^ ((6 : ℝ) * gamma * c * n)) *
          (2 : ℝ) ^ (11 - (c : ℝ) * n / 100) ≤
        (2 : ℝ) ^ 11 * (2 : ℝ) ^ (-(1 / 250 : ℝ) * n) := by
    have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have hexp : (6 : ℝ) * gamma * c * n +
          (11 - (c : ℝ) * n / 100) ≤
        11 + (-(1 / 250 : ℝ) * n) := by
      dsimp [gamma]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hcR) hn0]
    calc
      _ = (2 : ℝ) ^ ((6 : ℝ) * gamma * c * n +
          (11 - (c : ℝ) * n / 100)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (11 + (-(1 / 250 : ℝ) * n)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = _ := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num [Real.rpow_natCast]
  apply (positiveCoefficient_le p).trans
  calc
    _ ≤ eulerProduct⁻¹ ^ 2 *
          (2 : ℝ) ^ ((6 : ℝ) * gamma * c * n) *
            (2 : ℝ) ^ (11 - (c : ℝ) * n / 100) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by positivity [euler_positive]))
        (by positivity)
    _ ≤ eulerProduct⁻¹ ^ 2 *
        ((2 : ℝ) ^ 11 * (2 : ℝ) ^ (-(1 / 250 : ℝ) * n)) :=
      by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hmain
          (pow_nonneg (inv_nonneg.mpr euler_positive.le) 2)
    _ = _ := by ring

private def positiveIndexCode (n : ℕ) :
    RepeatedC3PositiveProfileIndex n → Fin (n + 1) × Fin (n + 1) :=
  fun p => (p.c, p.m)

private theorem positiveIndexCode_injective (n : ℕ) :
    Function.Injective (positiveIndexCode n) := by
  rintro ⟨c, m, hc, hm, hd⟩ ⟨c', m', hc', hm', hd'⟩ h
  simp only [positiveIndexCode, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

private theorem positiveIndex_card_le (n : ℕ) :
    Fintype.card (RepeatedC3PositiveProfileIndex n) ≤ (n + 1) ^ 2 := by
  have h := Fintype.card_le_of_injective (positiveIndexCode n)
    (positiveIndexCode_injective n)
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h

private theorem positiveKernel_row_eq (n : ℕ) :
    ∑ m ∈ Finset.range n, preE7SmallC3PositiveKernel n m =
      ∑ p : RepeatedC3PositiveProfileIndex n,
        preE7SmallC3PositiveCoefficient p := by
  unfold preE7SmallC3PositiveKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hpm : (p.m : ℕ) < n := by
    have hc : 0 < (p.c : ℕ) := p.c_pos
    have hn := p.degree_eq
    omega
  simp [hpm]

private theorem positiveKernel_row_eventually :
    ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.range n, preE7SmallC3PositiveKernel n m) ≤
        (4 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ 11) *
          (2 : ℝ) ^ (-(1 / 500 : ℝ) * n) := by
  have habsorb := eventually_shifted_natpow_mul_exponential_le 1 2
    (show (0 : ℝ) < 1 / 250 by norm_num)
  filter_upwards [positiveCoefficient_eventually, habsorb] with n hcoeff habsorb
  have habsorb' :
      (((n + 1 : ℕ) : ℝ) ^ 2) *
          (2 : ℝ) ^ (-(1 / 250 : ℝ) * n) ≤
        (4 : ℝ) * (2 : ℝ) ^ (-(1 / 500 : ℝ) * n) := by
    norm_num at habsorb ⊢
    exact habsorb
  rw [positiveKernel_row_eq]
  have hsum :
      (∑ p : RepeatedC3PositiveProfileIndex n,
        preE7SmallC3PositiveCoefficient p) ≤
      (Fintype.card (RepeatedC3PositiveProfileIndex n) : ℝ) *
        ((eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ 11) *
          (2 : ℝ) ^ (-(1 / 250 : ℝ) * n)) := by
    calc
      _ ≤ ∑ _p : RepeatedC3PositiveProfileIndex n,
          ((eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ 11) *
            (2 : ℝ) ^ (-(1 / 250 : ℝ) * n)) :=
        Finset.sum_le_sum (fun p _ => hcoeff p)
      _ = _ := by simp
  have hcard :
      (Fintype.card (RepeatedC3PositiveProfileIndex n) : ℝ) ≤
        (((n + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast positiveIndex_card_le n
  apply hsum.trans
  calc
    _ ≤ (((n + 1 : ℕ) : ℝ) ^ 2) *
        ((eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ 11) *
          (2 : ℝ) ^ (-(1 / 250 : ℝ) * n)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity [euler_positive])
    _ = (eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ 11) *
        ((((n + 1 : ℕ) : ℝ) ^ 2) *
          (2 : ℝ) ^ (-(1 / 250 : ℝ) * n)) := by ring
    _ ≤ (eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ 11) *
        ((4 : ℝ) * (2 : ℝ) ^ (-(1 / 500 : ℝ) * n)) :=
      mul_le_mul_of_nonneg_left habsorb' (by positivity [euler_positive])
    _ = _ := by norm_num; ring

private theorem pureLocalFactor_le (c : ℕ) :
    (((c + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (c * c / 4 + c)) ≤
      (((c + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ (((8 : ℝ) / 5) * ((c * c / 4 : ℕ) + c))) := by
  have h := positiveLocalFactor_le c 0
  norm_num at h ⊢
  exact h

private theorem pureExponent_le (c n : ℕ) (hn : 3 * c = n) :
    -((n : ℝ) ^ 2) / 16 + 5 * (n : ℝ) / 8 + 1 / 4 +
        (8 : ℝ) / 5 * ((c * c / 4 : ℕ) + c) ≤
      -(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
        139 * (n : ℝ) / 120 + 1 / 4 := by
  have hdivNat : (c * c / 4) * 4 ≤ c * c :=
    Nat.div_mul_le_self (c * c) 4
  have hdivR : ((c * c / 4 : ℕ) : ℝ) * 4 ≤ (c : ℝ) ^ 2 := by
    have hdivR' : ((c * c / 4 : ℕ) : ℝ) * 4 ≤
        (c : ℝ) * c := by exact_mod_cast hdivNat
    simpa only [pow_two] using hdivR'
  have hnR : (n : ℝ) = 3 * c := by exact_mod_cast hn.symm
  nlinarith

private theorem pureSummand_le {n : ℕ}
    (p : RepeatedC3PureProfileIndex n) :
    ((n.factorial : ℝ) *
        ((((p.c : ℕ) + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^ ((p.c : ℕ) * p.c / 4 + p.c))) /
          exactBenchmark n ≤
      eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ (n + 1)) *
        (2 : ℝ) ^ (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
          139 * (n : ℝ) / 120 + 1 / 4) := by
  let c := (p.c : ℕ)
  let E : ℝ := -((n : ℝ) ^ 2) / 16 + 5 * (n : ℝ) / 8 + 1 / 4
  let L : ℝ := (8 : ℝ) / 5 * ((c * c / 4 : ℕ) + c)
  have hn : 3 * c = n := p.degree_eq
  have hpoint := fusionWidthHot_pointing_denominator_le 0 n
  norm_num at hpoint
  have hlocal := pureLocalFactor_le c
  have hraw := mul_le_mul hpoint hlocal (by positivity)
    (by positivity [euler_positive])
  have hexp := pureExponent_le c n hn
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hpoly : (((n + 1 : ℕ) : ℝ) ^ n) * ((c + 1 : ℕ) : ℝ) ≤
      (((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by
    have hcn : c + 1 ≤ n + 1 := by omega
    have hcnR : ((c + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcn
    calc
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ n) * ((n + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcnR (by positivity)
      _ = _ := by rw [← pow_succ]
  have hbench := exactBenchmark_pos n
  have heq :
      ((n.factorial : ℝ) *
          (((c + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (c * c / 4 + c))) /
            exactBenchmark n =
        (((n.factorial : ℝ) / exactBenchmark n) *
          (((c + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (c * c / 4 + c))) := by
    field_simp [ne_of_gt hbench]
  rw [heq]
  apply hraw.trans
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
  have hmerge : (2 : ℝ) ^ E * (2 : ℝ) ^ L =
      (2 : ℝ) ^ (E + L) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 2) E L).symm
  rw [hcast]
  change
    (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) * (2 : ℝ) ^ E) *
      (((c + 1 : ℕ) : ℝ) * (2 : ℝ) ^ L) ≤ _
  calc
    _ = (eulerProduct⁻¹ *
          ((((n + 1 : ℕ) : ℝ) ^ n) * ((c + 1 : ℕ) : ℝ))) *
        ((2 : ℝ) ^ E * (2 : ℝ) ^ L) := by ac_rfl
    _ = (eulerProduct⁻¹ *
          ((((n + 1 : ℕ) : ℝ) ^ n) * ((c + 1 : ℕ) : ℝ))) *
        (2 : ℝ) ^ (E + L) := by rw [hmerge]
    _ ≤ (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ (n + 1))) *
        (2 : ℝ) ^ (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
          139 * (n : ℝ) / 120 + 1 / 4) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hpoly (inv_nonneg.mpr euler_positive.le))
        hpow (by positivity) (by positivity [euler_positive])
    _ = _ := by rfl

private def pureIndexCode (n : ℕ) :
    RepeatedC3PureProfileIndex n → Fin (n + 1) := fun p => p.c

private theorem pureIndexCode_injective (n : ℕ) :
    Function.Injective (pureIndexCode n) := by
  rintro ⟨c, hc, hd⟩ ⟨c', hc', hd'⟩ h
  simp only [pureIndexCode] at h
  cases h
  rfl

private theorem pureIndex_card_le (n : ℕ) :
    Fintype.card (RepeatedC3PureProfileIndex n) ≤ n + 1 := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective (pureIndexCode n)
      (pureIndexCode_injective n)

private theorem pureScalar_eventually :
    ∀ᶠ n : ℕ in atTop,
      preE7SmallC3PureScalar n ≤ eulerProduct⁻¹ *
        (2 : ℝ) ^ (-(1 / 1000 : ℝ) * n) := by
  let gamma : ℝ := 1 / 1000
  have hgamma : 0 < gamma := by norm_num [gamma]
  filter_upwards [eventually_succ_le_two_rpow hgamma,
    eventually_ge_atTop 100] with n hsucc hn100
  have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ (gamma * n) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hpoly0 := pow_le_pow_left₀ (by positivity) hsucc (n + 2)
  have hpoly : (((n + 1 : ℕ) : ℝ) ^ (n + 2)) ≤
      (2 : ℝ) ^ (gamma * n * (n + 2)) := by
    calc
      _ ≤ ((2 : ℝ) ^ (gamma * n)) ^ (n + 2) := hpoly0
      _ = _ := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        push_cast
        congr 1 <;> ring
  have hexp : gamma * (n : ℝ) * (n + 2) +
        (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
          139 * (n : ℝ) / 120 + 1 / 4) ≤
      -(1 / 1000 : ℝ) * n := by
    have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn100
    dsimp [gamma]
    nlinarith [sq_nonneg ((n : ℝ) - 100)]
  have hpow :
      (2 : ℝ) ^ (gamma * (n : ℝ) * (n + 2)) *
          (2 : ℝ) ^ (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
            139 * (n : ℝ) / 120 + 1 / 4) ≤
        (2 : ℝ) ^ (-(1 / 1000 : ℝ) * n) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  unfold preE7SmallC3PureScalar
  have hsum :
      (∑ p : RepeatedC3PureProfileIndex n,
        ((n.factorial : ℝ) *
          ((((p.c : ℕ) + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^ ((p.c : ℕ) * p.c / 4 + p.c))) /
            exactBenchmark n) ≤
      (Fintype.card (RepeatedC3PureProfileIndex n) : ℝ) *
        (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ (n + 1)) *
          (2 : ℝ) ^ (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
            139 * (n : ℝ) / 120 + 1 / 4)) := by
    calc
      _ ≤ ∑ p : RepeatedC3PureProfileIndex n,
          (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ (n + 1)) *
            (2 : ℝ) ^ (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
              139 * (n : ℝ) / 120 + 1 / 4)) :=
        Finset.sum_le_sum (fun p _ => pureSummand_le p)
      _ = _ := by simp
  have hcard : (Fintype.card (RepeatedC3PureProfileIndex n) : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) := by exact_mod_cast pureIndex_card_le n
  apply hsum.trans
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) *
        (eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ (n + 1)) *
          (2 : ℝ) ^ (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
            139 * (n : ℝ) / 120 + 1 / 4)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity [euler_positive])
    _ = eulerProduct⁻¹ * ((((n + 1 : ℕ) : ℝ) ^ (n + 2)) *
        (2 : ℝ) ^ (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
          139 * (n : ℝ) / 120 + 1 / 4)) := by
      rw [pow_succ']
      ring
    _ ≤ eulerProduct⁻¹ *
        ((2 : ℝ) ^ (gamma * n * (n + 2)) *
          (2 : ℝ) ^ (-(13 : ℝ) * (n : ℝ) ^ 2 / 720 +
            139 * (n : ℝ) / 120 + 1 / 4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpoly (by positivity))
        (inv_nonneg.mpr euler_positive.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (inv_nonneg.mpr euler_positive.le)

/-- Complete forward estimate for the global degree-three packet.  Its
positive tails recurse only to their literal smaller complement degree; the
empty-tail endpoint is the exponentially decaying scalar. -/
noncomputable def preE7SmallC3Packet_exponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7SmallC3PacketRatio := by
  let es := eventually_atTop.mp pureScalar_eventually
  let er := eventually_atTop.mp positiveKernel_row_eventually
  let Ns : ℕ := es.choose
  let Nr : ℕ := er.choose
  have hs := es.choose_spec
  have hr := er.choose_spec
  let Cs : ℝ := eulerProduct⁻¹
  let Cr : ℝ := 4 * eulerProduct⁻¹ ^ 2 * (2 : ℝ) ^ 11
  refine
    { scalar := preE7SmallC3PureScalar
      kernel := preE7SmallC3PositiveKernel
      threshold := max Ns Nr
      rate := 1 / 1000
      scalarConst := Cs
      rowConst := Cr
      rate_pos := by norm_num
      scalarConst_pos := by dsimp [Cs]; positivity [euler_positive]
      rowConst_nonneg := by dsimp [Cr]; positivity [euler_positive]
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n hn m hm
    exact preE7SmallC3PositiveKernel_nonneg n m
  · intro n hn
    exact preE7SmallC3PacketRatio_recurrence
      hChief hWeight hPrimitive h18 n
  · intro n hn
    exact hs n ((le_max_left Ns Nr).trans hn)
  · intro n hn
    have hrow := hr n ((le_max_right Ns Nr).trans hn)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hpow :
        (2 : ℝ) ^ (-(1 / 500 : ℝ) * n) ≤
          (2 : ℝ) ^ (-(1 / 1000 : ℝ) * n) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith
    exact hrow.trans (mul_le_mul_of_nonneg_left hpow
      (by positivity [euler_positive]))

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
