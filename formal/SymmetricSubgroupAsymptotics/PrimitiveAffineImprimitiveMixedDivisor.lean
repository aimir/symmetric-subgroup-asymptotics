import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallPrimeSources

/-!
# Mixed-divisor affine capacity bounds

Different elementary characteristics may use different prime-power divisors
of the actual block count.  The pointwise minimum below records that fact in
the literal chief tower.  It is needed, for example, at local degree nine and
twenty-four blocks: binary factors use the ternary divisor while ternary
factors use the binary divisor.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

namespace ActualWreathCompressionTower

/-- Two simultaneous capacity-rate bounds may be combined pointwise. -/
theorem capacityRateBound_min
    (r₁ r₂ : ℕ → ℝ) :
    {S : ActualWreathCompressionState Q I} →
      (T : ActualWreathCompressionTower S) →
      T.CapacityRateBound r₁ → T.CapacityRateBound r₂ →
      T.CapacityRateBound (fun p => min (r₁ p) (r₂ p))
  | _, .terminal _ _, _, _ => trivial
  | _, @ActualWreathCompressionTower.elementary _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C H capacity_le_half capacity_le_log
        capacity_refined coefficient_le next, h₁, h₂ => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      constructor
      · rw [mul_min_of_nonneg _ _ (by positivity)]
        exact le_min h₁.1 h₂.1
      · exact capacityRateBound_min r₁ r₂ next h₁.2 h₂.2
  | _, @ActualWreathCompressionTower.semisimple _ _ _ _ _ _ _ _ D'
      groupD' finiteD' phi hphi C next, h₁, h₂ => by
      letI : Group D' := groupD'
      letI : Finite D' := finiteD'
      exact capacityRateBound_min r₁ r₂ next h₁ h₂

end ActualWreathCompressionTower

namespace Non2UnipotentPrefixFiniteMenu

/-- Exact-parity version of the common affine margin conversion. -/
theorem smallAffine_even_budget_margin
    (r s w : ℕ) (hw : w = r * s) (hweven : Even w)
    (k eta : ℝ)
    (hnum : preE7CharacterRho * (r : ℝ) + k ≤ ((r : ℝ) - 1) / 8)
    (heta : eta ≤ k * s) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - s) / 8 - eta := by
  have hew : evenWidth w = w := by
    rcases hweven with ⟨a, rfl⟩
    unfold evenWidth halfDegree
    omega
  have hwR : (w : ℝ) = r * s := by exact_mod_cast hw
  rw [hew, hwR]
  ring_nf at hnum heta ⊢
  nlinarith

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

private abbrev blocks := Nat.card block.Points

/-- Construction-facing source using two different exact primary divisors. -/
noncomputable def of_twoTraceyPrimary
    (q₁ e₁ q₂ e₂ n : ℕ)
    (hq₁ : q₁.Prime) (he₁ : 1 ≤ e₁)
    (hdiv₁ : q₁ ^ e₁ ∣ blocks block)
    (hmax₁ : ¬ q₁ ^ (e₁ + 1) ∣ blocks block)
    (hq₂ : q₂.Prime) (he₂ : 1 ≤ e₂)
    (hdiv₂ : q₂ ^ e₂ ∣ blocks block)
    (hmax₂ : ¬ q₂ ^ (e₂ + 1) ∣ blocks block)
    (hn : n ≠ 0) (hcomponent : Nat.card block.Component ∣ n)
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - blocks block) / 8 -
        refinedWeightedFactorBudget
          (fun p => min
            (ActualWreathCompressionTower.traceyPrimaryRate
              (blocks block) q₁ e₁ p)
            (ActualWreathCompressionTower.traceyPrimaryRate
              (blocks block) q₂ e₂ p)) n) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P := by
  apply of_refinedFactorBudget hTraceyHalf hTraceyLog hTraceyRefined
    hTraceyPerm block P _
      (fun p => le_min
        (ActualWreathCompressionTower.traceyPrimaryRate_nonneg
          (blocks block) q₁ e₁ p)
        (ActualWreathCompressionTower.traceyPrimaryRate_nonneg
          (blocks block) q₂ e₂ p))
      n hn hcomponent
  · let T := tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block
    apply ActualWreathCompressionTower.capacityRateBound_min _ _ T
    · simpa only [Fintype.card_eq_nat_card] using
        (ActualWreathCompressionTower.capacityRateBound_traceyPrimary
          q₁ e₁ hq₁ he₁
          (by simpa only [Fintype.card_eq_nat_card] using hdiv₁)
          (by simpa only [Fintype.card_eq_nat_card] using hmax₁) T)
    · simpa only [Fintype.card_eq_nat_card] using
        (ActualWreathCompressionTower.capacityRateBound_traceyPrimary
          q₂ e₂ hq₂ he₂
          (by simpa only [Fintype.card_eq_nat_card] using hdiv₂)
          (by simpa only [Fintype.card_eq_nat_card] using hmax₂) T)
  · exact hmargin

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
