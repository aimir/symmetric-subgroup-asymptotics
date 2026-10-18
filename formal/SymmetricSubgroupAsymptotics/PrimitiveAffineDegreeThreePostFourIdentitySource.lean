import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientEndpoint

/-!
# Identity-comparator closure at six and twelve blocks

At six and twelve blocks, a ternary capacity at most one leaves enough
margin to retain the literal signed quotient in its faithful action on the
`2s` nonzero block points.  This file proves that numerical step once, so a
later signed-isotype argument only has to supply the capacity-one theorem.

The eighteen-block case is intentionally absent: its identity comparator
has degree thirty-six and does not leave the required margin at the known
capacity bounds.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The literal signed quotient action has degree twice the block count in
local degree three. -/
theorem degreeThree_quotientDegree_eq_twice_blocks
    (hr : Nat.card block.Fibre = 3) :
    quotientDegree block = 2 * Nat.card block.Points := by
  rw [quotientDegree_eq block, hr]

/-- At six and twelve blocks, capacity one permits the actual signed
quotient itself to be used as the faithful terminal comparator. -/
noncomputable def degreeThreeSixOrTwelveIdentitySource_of_capacity_one
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6 ∨ Nat.card block.Points = 12)
    (hcap :
      (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm).capacity ≤ 1) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply degreeThreeIdentitySignedQuotientSource block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr (quotientDegree block)
    (quotientAction block P) (quotientAction_injective block P)
  · have hs2 : 2 ≤ Nat.card block.Points := by
      rcases hs with h | h <;> omega
    rw [degreeThree_quotientDegree_eq_twice_blocks block hr]
    omega
  · let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm
    have hw : w = 3 * Nat.card block.Points := by
      simpa only [hr] using width_eq block
    have hq := degreeThree_quotientDegree_eq_twice_blocks block hr
    have hlog : Real.logb 2 3 ≤ 8 / 5 := by
      have hp : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
      have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
        (by positivity : (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ)) hp
      simp only [Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2 (by
        simpa only [mul_comm] using le_of_lt h)
    have hrate0 : 0 ≤ Real.logb 2 3 / 3 :=
      div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num))
        (by norm_num)
    have hcost : Real.logb 2 3 / 3 * H.capacity ≤ 8 / 15 := by
      calc
        Real.logb 2 3 / 3 * H.capacity ≤
            Real.logb 2 3 / 3 * 1 :=
          mul_le_mul_of_nonneg_left hcap hrate0
        _ ≤ 8 / 15 := by linarith
    rcases hs with hs | hs
    · have hw18 : w = 18 := by simpa only [hs] using hw
      have hq12 : quotientDegree block = 12 := by
        simpa only [hs] using hq
      have hw18R : (w : ℝ) = 18 := by exact_mod_cast hw18
      have heven : evenWidth w = 18 := by
        rw [hw18]
        norm_num [evenWidth, halfDegree]
      rw [hw18R, heven, hq12]
      norm_num [preE7CharacterRho, evenWidth, halfDegree]
      linarith
    · have hw36 : w = 36 := by simpa only [hs] using hw
      have hq24 : quotientDegree block = 24 := by
        simpa only [hs] using hq
      have hw36R : (w : ℝ) = 36 := by exact_mod_cast hw36
      have heven : evenWidth w = 36 := by
        rw [hw36]
        norm_num [evenWidth, halfDegree]
      rw [hw36R, heven, hq24]
      norm_num [preE7CharacterRho, evenWidth, halfDegree]
      linarith

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
