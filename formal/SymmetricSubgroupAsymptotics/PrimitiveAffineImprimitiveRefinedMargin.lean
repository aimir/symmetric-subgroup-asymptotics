import SymmetricSubgroupAsymptotics.ActualWreathCompressionRefinedBudget
import SymmetricSubgroupAsymptotics.ActualWreathCompressionIntegralRefinedBudget
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallOrder

/-!
# Refined affine-component margins

This file turns the prime-by-prime retained Tracey budget into the literal
`ComponentSource` used by the imprimitive affine transfer.  The component
order is charged by divisibility, so no abstract affine overgroup replaces
the actual local component.  Two constructors expose the useful choices:
an exact primary divisor of the block count, and an exact prime-power block
count.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- A nonnegative retained rate, an exact component-order divisor, and the
corresponding scalar inequality produce the construction-facing source. -/
noncomputable def of_refinedFactorBudget
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    (n : ℕ) (hn : n ≠ 0)
    (hdiv : Nat.card block.Component ∣ n)
    (hcapacity :
      let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
      T.CapacityRateBound rate)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        refinedWeightedFactorBudget rate n) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P where
  margin := by
    let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    have heta0 : T.envelope.eta ≤
        refinedWeightedFactorBudget rate (Nat.card block.Component) :=
      T.envelope_eta_le_refinedFactorBudget_card rate hrate hcapacity
    have heta : T.envelope.eta ≤ refinedWeightedFactorBudget rate n :=
      heta0.trans (refinedWeightedFactorBudget_mono_of_dvd rate hrate
        (Nat.card_pos (α := block.Component)).ne' hn hdiv)
    have hv : T.envelope.v = Nat.card block.Points := by
      simpa only [T, tower, Fintype.card_eq_nat_card] using
        ActualWreathCompressionTower.envelope_v T
    change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - T.envelope.v) / 8 - T.envelope.eta
    rw [hv]
    linarith

/-- Integral version of `of_refinedFactorBudget`.  The actual trace records
natural capacities, so equal-characteristic chief factors are combined before
the floor is taken.  This is the sharp construction needed by the finite
small-affine catalogue. -/
noncomputable def of_integralRefinedFactorBudget
    (rate : ℕ → ℝ) (hrate : ∀ p, 0 ≤ rate p)
    (n : ℕ) (hn : n ≠ 0)
    (hdiv : Nat.card block.Component ∣ n)
    (hcapacity :
      let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
      T.CapacityRateBound rate)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        integralRefinedWeightedFactorBudget rate n) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P where
  margin := by
    let tr := trace hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    have hintegral : T.IntegralCapacities := by
      simpa only [T, tower, tr, trace] using tr.integralCapacities
    have heta : T.envelope.eta ≤ integralRefinedWeightedFactorBudget rate n :=
      T.envelope_eta_le_integralRefinedFactorBudget_of_dvd hintegral rate hrate
        hcapacity n hn hdiv
    have hv : T.envelope.v = Nat.card block.Points := by
      simpa only [T, tower, Fintype.card_eq_nat_card] using
        ActualWreathCompressionTower.envelope_v T
    change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - T.envelope.v) / 8 - T.envelope.eta
    rw [hv]
    linarith

/-- Integral construction using Tracey's sharp primary rate. -/
noncomputable def of_integralTraceyPrimary
    (q e n : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ Nat.card block.Points)
    (hqmax : ¬ q ^ (e + 1) ∣ Nat.card block.Points)
    (hn : n ≠ 0) (hdiv : Nat.card block.Component ∣ n)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        integralRefinedWeightedFactorBudget
          (ActualWreathCompressionTower.traceyPrimaryRate
            (Nat.card block.Points) q e) n) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  apply of_integralRefinedFactorBudget hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P
      (ActualWreathCompressionTower.traceyPrimaryRate
        (Nat.card block.Points) q e)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg
        (Nat.card block.Points) q e) n hn hdiv
  · let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    simpa only [Fintype.card_eq_nat_card] using
      (ActualWreathCompressionTower.capacityRateBound_traceyPrimary
        q e hq he (by simpa only [Fintype.card_eq_nat_card] using hqdiv)
          (by simpa only [Fintype.card_eq_nat_card] using hqmax) T)
  · exact hmargin

/-- Integral construction at an exact prime-power block count. -/
noncomputable def of_integralTraceyPrimePower
    (q e n : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hs : Nat.card block.Points = q ^ e)
    (hn : n ≠ 0) (hdiv : Nat.card block.Component ∣ n)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        integralRefinedWeightedFactorBudget
          (ActualWreathCompressionTower.traceyPrimePowerRate q e) n) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  apply of_integralRefinedFactorBudget hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P
      (ActualWreathCompressionTower.traceyPrimePowerRate q e)
      (ActualWreathCompressionTower.traceyPrimePowerRate_nonneg q e)
      n hn hdiv
  · let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    simpa only [Fintype.card_eq_nat_card] using
      (ActualWreathCompressionTower.capacityRateBound_traceyPrimePower
        q e hq he (by simpa only [Fintype.card_eq_nat_card] using hs) T)
  · exact hmargin

/-- Select Tracey's sharp primary bound at an exact prime-power divisor of
the block count and the prime-to bound in every other characteristic. -/
noncomputable def of_traceyPrimary
    (q e n : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hqdiv : q ^ e ∣ Nat.card block.Points)
    (hqmax : ¬ q ^ (e + 1) ∣ Nat.card block.Points)
    (hn : n ≠ 0) (hdiv : Nat.card block.Component ∣ n)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        refinedWeightedFactorBudget
          (ActualWreathCompressionTower.traceyPrimaryRate
            (Nat.card block.Points) q e) n) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  apply of_refinedFactorBudget hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P
      (ActualWreathCompressionTower.traceyPrimaryRate
        (Nat.card block.Points) q e)
      (ActualWreathCompressionTower.traceyPrimaryRate_nonneg
        (Nat.card block.Points) q e) n hn hdiv
  · let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    simpa only [Fintype.card_eq_nat_card] using
      (ActualWreathCompressionTower.capacityRateBound_traceyPrimary
        q e hq he (by simpa only [Fintype.card_eq_nat_card] using hqdiv)
          (by simpa only [Fintype.card_eq_nat_card] using hqmax) T)
  · exact hmargin

/-- At an exact prime-power block count, select the soluble-transitive
central-binomial rate in the matching characteristic. -/
noncomputable def of_traceyPrimePower
    (q e n : ℕ) (hq : q.Prime) (he : 1 ≤ e)
    (hs : Nat.card block.Points = q ^ e)
    (hn : n ≠ 0) (hdiv : Nat.card block.Component ∣ n)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        refinedWeightedFactorBudget
          (ActualWreathCompressionTower.traceyPrimePowerRate q e) n) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  apply of_refinedFactorBudget hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P
      (ActualWreathCompressionTower.traceyPrimePowerRate q e)
      (ActualWreathCompressionTower.traceyPrimePowerRate_nonneg q e)
      n hn hdiv
  · let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P
    simpa only [Fintype.card_eq_nat_card] using
      (ActualWreathCompressionTower.capacityRateBound_traceyPrimePower
        q e hq he (by simpa only [Fintype.card_eq_nat_card] using hs) T)
  · exact hmargin

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
