import SymmetricSubgroupAsymptotics.MarkedC4SolubleReduction
import SymmetricSubgroupAsymptotics.MarkedC4AsymptoticTransfer
import SymmetricSubgroupAsymptotics.FusionHot

/-!
# From the soluble marked moment to the global marked moment

The preceding file proved the literal inequality

`M4(b,r) ≤ b! * 4^r * M4_sol(b,r)`.

Here the factorial and the one-generator mark cost are absorbed uniformly
into the quadratic epsilon.  Therefore the only remaining global reduction
obligation is the soluble marked moment; the final RDT one-generator step is
fully discharged.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

/-- The same marked quadratic bound restricted to soluble permutation
subgroups. -/
def SolubleGlobalMarkedC4MomentBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
    (r : ℝ) ≤ K * b →
    solubleMarkedC4Moment b r ≤
      (2 : ℝ) ^ (markedF b r + ε * ((b : ℝ) + r) ^ 2)

/-- The multiplicity `b! 4^r` of the final one-generator code is uniformly
quadratically negligible when `r/b` is bounded. -/
theorem eventually_factorial_mul_fourPow_le_quadratic
    (δ K : ℝ) (hδ : 0 < δ) :
    ∀ᶠ b : ℕ in atTop, ∀ r : ℕ, (r : ℝ) ≤ K * b →
      (Nat.factorial b : ℝ) * (2 : ℝ) ^ (2 * r) ≤
        (2 : ℝ) ^ (δ * ((b : ℝ) + r) ^ 2) := by
  let Kpos : ℝ := max K 0
  have hKpos : 0 ≤ Kpos := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ (1 / Real.log 2 : ℝ) := by positivity
  have hlog := MarkerDefectSum.eventually_log_error_le_linear
    (1 / Real.log 2) hC (show 0 < δ / 4 by positivity)
  have hlinear := eventually_linear_add_le_quadratic
    (a := δ / 4) (C := 2 * Kpos) (K := 0)
    (show 0 < δ / 4 by positivity) (mul_nonneg (by norm_num) hKpos)
      (show 0 ≤ (0 : ℝ) by norm_num)
  filter_upwards [hlog, hlinear] with b hlog hlinear
  intro r hr
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hKr : (r : ℝ) ≤ Kpos * b := by
    exact hr.trans (mul_le_mul_of_nonneg_right (le_max_left K 0) hb0)
  have hfacNat : Nat.factorial b ≤ (b + 2) ^ b := by
    exact b.factorial_le_pow.trans
      (Nat.pow_le_pow_left (Nat.le_add_right b 2) b)
  have hfacCast : (Nat.factorial b : ℝ) ≤ ((b : ℝ) + 2) ^ b := by
    exact_mod_cast hfacNat
  have hpowlog : ((b : ℝ) + 2) ^ b =
      (2 : ℝ) ^ (((b : ℝ) / Real.log 2) *
        Real.log ((b : ℝ) + 2)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp [hlog2.ne']
  have hfac : (Nat.factorial b : ℝ) ≤
      (2 : ℝ) ^ (((b : ℝ) / Real.log 2) *
        Real.log ((b : ℝ) + 2)) := hfacCast.trans_eq hpowlog
  have hfacExp : ((b : ℝ) / Real.log 2) *
        Real.log ((b : ℝ) + 2) ≤ (δ / 4) * (b : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hlog hb0
    calc
      ((b : ℝ) / Real.log 2) * Real.log ((b : ℝ) + 2) =
          (b : ℝ) * ((1 / Real.log 2) * Real.log ((b : ℝ) + 2)) := by
        ring
      _ ≤ (b : ℝ) * ((δ / 4) * b) := hm
      _ = (δ / 4) * (b : ℝ) ^ 2 := by ring
  have hmarkExp : (2 : ℝ) * r ≤ (δ / 4) * (b : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hKr (show 0 ≤ (2 : ℝ) by norm_num)
    dsimp [Kpos] at hlinear hm
    nlinarith
  calc
    (Nat.factorial b : ℝ) * (2 : ℝ) ^ (2 * r) ≤
        (2 : ℝ) ^ (((b : ℝ) / Real.log 2) *
          Real.log ((b : ℝ) + 2)) * (2 : ℝ) ^ (2 * r) :=
      mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = (2 : ℝ) ^ ((((b : ℝ) / Real.log 2) *
          Real.log ((b : ℝ) + 2)) + (2 : ℝ) * r) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_cast
    _ ≤ (2 : ℝ) ^ (δ * ((b : ℝ) + r) ^ 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hsquare : (b : ℝ) ^ 2 ≤ ((b : ℝ) + r) ^ 2 := by
        nlinarith [mul_nonneg hb0 hr0]
      have hsum : ((b : ℝ) / Real.log 2) *
            Real.log ((b : ℝ) + 2) + (2 : ℝ) * r ≤
          (δ / 2) * (b : ℝ) ^ 2 := by
        linarith
      calc
        _ ≤ (δ / 2) * (b : ℝ) ^ 2 := hsum
        _ ≤ δ * ((b : ℝ) + r) ^ 2 := by
          nlinarith

/-- RDT's one-generator theorem plus a soluble marked bound prove the full
global marked moment. -/
theorem globalMarkedC4MomentBound_of_soluble
    (hRDT : RDTOneGeneratorSolubleInput)
    (hsol : SolubleGlobalMarkedC4MomentBound) :
    Non2UnipotentPrefixFiniteMenu.GlobalMarkedC4MomentBound := by
  intro ε hε K
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [hsol (ε / 2) hhalf K,
    eventually_factorial_mul_fourPow_le_quadratic (ε / 2) K hhalf]
      with b hsolb hover
  intro r hr
  have hsolbr := hsolb r hr
  have hover' := hover r hr
  have hsolnonneg : 0 ≤ solubleMarkedC4Moment b r := by
    unfold solubleMarkedC4Moment
    positivity
  have hglobal := markedC4Moment_le_factorial_mul_solubleMoment hRDT b r
  calc
    Non2UnipotentPrefixFiniteMenu.markedC4Moment b r ≤
        (Nat.factorial b : ℝ) * (2 : ℝ) ^ (2 * r) *
          solubleMarkedC4Moment b r := hglobal
    _ ≤ (2 : ℝ) ^ ((ε / 2) * ((b : ℝ) + r) ^ 2) *
          (2 : ℝ) ^ (markedF b r +
            (ε / 2) * ((b : ℝ) + r) ^ 2) :=
      mul_le_mul hover' hsolbr hsolnonneg (by positivity)
    _ = (2 : ℝ) ^ (markedF b r + ε * ((b : ℝ) + r) ^ 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end MarkedC4
end SymmetricSubgroupAsymptotics

end
