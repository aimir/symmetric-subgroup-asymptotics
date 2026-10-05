import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRawExceptionalGrowth

/-!
# A fixed ternary prepend preserves a raw quadratic deficit

Degree-two pair packages retain their exceptional term before physical
pointing, with a strict deficit from the universal `b^2 / 16` exponent.
This file proves the reusable numerical fact needed by every degree-three
affine residual row: multiplying that term by one fixed ternary-layer
coefficient and one fixed linear exponential still gives an exponentially
decaying scalar after pointing at the original physical width.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A fixed-width pointing factor cancels the universal quadratic term in
a raw exceptional estimate.  The remaining strict quadratic deficit absorbs
both the arbitrary-width factorial loss and every fixed linear prepend. -/
noncomputable def rawQuadraticExceptional_fixedPrepend
    {w : ℕ} {U : PreE7NonPairActionClass w}
    {X : ℕ → ℝ}
    (R : RawQuadraticExceptionalBound X)
    (hX : ∀ b, 0 ≤ X b)
    {C tau : ℝ} (hC : 0 ≤ C) (htau : 0 ≤ tau) :
    ExponentialScalarBound (fun b ↦
      growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
        ((C * (2 : ℝ) ^ (tau * b)) * X b)) := by
  let gamma : ℝ := R.rate / 8
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact div_pos R.rate_pos (by norm_num : (0 : ℝ) < 8)
  let hs := eventually_atTop.mp (eventually_succ_le_two_rpow hgamma)
  let Ns : ℕ := Classical.choose hs
  have hNs : ∀ b ≥ Ns, ((b + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (gamma * (b : ℝ)) :=
    Classical.choose_spec hs
  let linear : ℝ := tau + 2 * gamma * w + 5 / 8
  let constant : ℝ := gamma * (w : ℝ) ^ 2 + 5 * w / 8 + 1 / 4
  have hlinear : 0 ≤ linear := by
    dsimp [linear]
    positivity
  have hconstant : 0 ≤ constant := by
    dsimp [constant]
    positivity
  let hl := eventually_atTop.mp
    (eventually_linear_add_le_quadratic
      (div_pos R.rate_pos (by norm_num : (0 : ℝ) < 8))
      hlinear hconstant)
  let Nl : ℕ := Classical.choose hl
  have hNl := Classical.choose_spec hl
  let N : ℕ := max R.threshold (max Ns (max Nl 1))
  let K : ℝ := eulerProduct⁻¹ * C * R.constant
  refine
    { threshold := N
      rate := R.rate / 2
      constant := K + 1
      rate_pos := div_pos R.rate_pos (by norm_num : (0 : ℝ) < 2)
      constant_pos := by
        have hK : 0 ≤ K := by
          dsimp [K]
          exact mul_nonneg
            (mul_nonneg (inv_nonneg.mpr euler_positive.le) hC)
            R.constant_pos.le
        linarith
      bound := ?_ }
  intro b hb
  have hbR : R.threshold ≤ b := (le_max_left _ _).trans hb
  have hbNs : Ns ≤ b + w := by
    have : Ns ≤ b := (le_max_left Ns (max Nl 1)).trans
      ((le_max_right R.threshold (max Ns (max Nl 1))).trans hb)
    omega
  have hbNl : Nl ≤ b := by
    exact (le_max_left Nl 1).trans
      ((le_max_right Ns (max Nl 1)).trans
        ((le_max_right R.threshold (max Ns (max Nl 1))).trans hb))
  have hb1 : 1 ≤ b := by
    exact (le_max_right Nl 1).trans
      ((le_max_right Ns (max Nl 1)).trans
        ((le_max_right R.threshold (max Ns (max Nl 1))).trans hb))
  have hsucc := hNs (b + w) hbNs
  have hpoly : (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) ≤
      (2 : ℝ) ^ (gamma * ((b + w : ℕ) : ℝ) ^ 2) := by
    have hp := pow_le_pow_left₀ (by positivity) hsucc (b + w)
    calc
      (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) ≤
          (((2 : ℝ) ^ (gamma * ((b + w : ℕ) : ℝ))) ^
            (b + w)) := hp
      _ = (2 : ℝ) ^ (gamma * ((b + w : ℕ) : ℝ) ^ 2) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        push_cast
        congr 1
        ring
  have hsmall := hNl b hbNl
  have hexponent :
      gamma * ((b + w : ℕ) : ℝ) ^ 2 +
          (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4) +
          tau * b + (((1 / 16 : ℝ) - R.rate) * (b : ℝ) ^ 2) ≤
        -(3 * R.rate / 4) * (b : ℝ) ^ 2 := by
    dsimp [gamma, linear, constant] at hsmall ⊢
    push_cast at hsmall ⊢
    ring_nf at hsmall ⊢
    nlinarith [hsmall]
  have hquadratic :
      -(3 * R.rate / 4) * (b : ℝ) ^ 2 ≤
        -(R.rate / 2) * b := by
    have hbR1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
    have hb0 : (0 : ℝ) ≤ b := by positivity
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hbR1)]
  have hA : (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
      (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
      (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))))
  have hpoint0 := fusionWidthHot_pointing_denominator_le b w
  have hpoint : growingQuotientNormalizedPointing b w
      (Nat.card (Subgroup.normalizer
        (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) ≤
      eulerProduct⁻¹ * (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) *
        (2 : ℝ) ^ (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
          5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4) := by
    unfold growingQuotientNormalizedPointing
    calc
      _ ≤ (((b + w).factorial : ℝ) / (b.factorial : ℝ)) /
          exactBenchmark (b + w) := by
        have hnum : 0 ≤ (((b + w).factorial : ℝ) /
            (b.factorial : ℝ)) := by positivity
        have hbench : 0 < exactBenchmark (b + w) :=
          exactBenchmark_pos (b + w)
        apply div_le_div_of_nonneg_right _ hbench.le
        exact div_le_self hnum hA
      _ ≤ _ := hpoint0
  have hraw := R.bound b hbR
  have hpointUpper : 0 ≤
      eulerProduct⁻¹ * (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) *
        (2 : ℝ) ^ (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
          5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4) := by
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr euler_positive.le)
        (pow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hrawUpper : 0 ≤ R.constant *
      (2 : ℝ) ^ (((1 / 16 : ℝ) - R.rate) * (b : ℝ) ^ 2) := by
    exact mul_nonneg R.constant_pos.le
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hprepend : 0 ≤ C * (2 : ℝ) ^ (tau * b) := by positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr euler_positive.le) hC)
      R.constant_pos.le
  calc
    growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w U : Set (Equiv.Perm (Fin w)))) : ℝ) *
        ((C * (2 : ℝ) ^ (tau * b)) * X b) ≤
        (eulerProduct⁻¹ * (((b + w + 1 : ℕ) : ℝ) ^ (b + w)) *
          (2 : ℝ) ^ (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4)) *
          ((C * (2 : ℝ) ^ (tau * b)) *
            (R.constant * (2 : ℝ) ^
              (((1 / 16 : ℝ) - R.rate) * (b : ℝ) ^ 2))) := by
      exact mul_le_mul hpoint
        (mul_le_mul_of_nonneg_left hraw hprepend)
        (mul_nonneg hprepend (hX b)) hpointUpper
    _ ≤ (eulerProduct⁻¹ *
          (2 : ℝ) ^ (gamma * ((b + w : ℕ) : ℝ) ^ 2) *
          (2 : ℝ) ^ (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4)) *
          ((C * (2 : ℝ) ^ (tau * b)) *
            (R.constant * (2 : ℝ) ^
              (((1 / 16 : ℝ) - R.rate) * (b : ℝ) ^ 2))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly
            (inv_nonneg.mpr euler_positive.le)) (by positivity))
        (mul_nonneg hprepend hrawUpper)
    _ = K * (2 : ℝ) ^
        (gamma * ((b + w : ℕ) : ℝ) ^ 2 +
          (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
            5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4) +
          tau * b + (((1 / 16 : ℝ) - R.rate) * (b : ℝ) ^ 2)) := by
      dsimp [K]
      calc
        _ = (eulerProduct⁻¹ * C * R.constant) *
            (((2 : ℝ) ^ (gamma * ((b + w : ℕ) : ℝ) ^ 2) *
              (2 : ℝ) ^ (-((b + w : ℕ) : ℝ) ^ 2 / 16 +
                5 * ((b + w : ℕ) : ℝ) / 8 + 1 / 4)) *
             ((2 : ℝ) ^ (tau * b) *
              (2 : ℝ) ^ (((1 / 16 : ℝ) - R.rate) *
                (b : ℝ) ^ 2))) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          ring_nf
    _ ≤ K * (2 : ℝ) ^ (-(3 * R.rate / 4) * (b : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) hK
    _ ≤ K * (2 : ℝ) ^ (-(R.rate / 2) * b) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hquadratic) hK
    _ ≤ (K + 1) * (2 : ℝ) ^ (-(R.rate / 2) * b) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)

namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Exceptional decay for an arbitrary literal pair growth package after
the actual ternary layer has been prepended. -/
noncomputable def prependSignedQuotientGrowth_exceptional
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (G : PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction w U ⧸ E block P))
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    let S := prependSignedQuotientSummedSource block P H
      G.package.envelope G.package.v G.package.action
        G.package.action_injective
    ExponentialScalarBound S.exceptionalScalar := by
  let tau : ℝ := Real.logb 2 (elementaryChart block P).p /
    (elementaryChart block P).p * H.capacity
  have htau : 0 ≤ tau := by
    dsimp [tau]
    have hlog : 0 ≤ Real.logb 2 (elementaryChart block P).p :=
      Real.logb_nonneg (by norm_num)
        (by exact_mod_cast (elementaryChart block P).p_prime.one_le)
    exact mul_nonneg (div_nonneg hlog (by positivity)) H.capacity_nonneg
  let R := G.exceptionalGrowth hcoarse
  let S := prependSignedQuotientSummedSource block P H
    G.package.envelope G.package.v G.package.action
      G.package.action_injective
  have h := rawQuadraticExceptional_fixedPrepend
    (U := U) R G.package.envelope.exceptionalRaw_nonneg
    H.coefficient_nonneg htau
  simpa only [S, PreE7DegreeTwoPairSummedSource.exceptionalScalar,
    prependSignedQuotientSummedSource, tau] using h

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
