import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeTopKernelZeroSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientEndpoint

/-!
# The zero signed-kernel four-block cell

The Sylow-width sharpening used for the other zero-kernel block counts is
not useful at four blocks: the block top has no ternary orbit saving.  The
original refined Tracey row is sharper here.  Its binary-square clause gives
capacity one, and the faithful literal four-point top then leaves a strict
original-weight margin at physical width twelve.
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

/-- At four blocks, use the faithful literal block top with the unsharpened
capacity-one ternary row. -/
noncomputable def degreeThreeFourBlockKernelZeroSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hK : degreeNineLinearBlockKernel block P = ⊥) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  apply degreeThreeIdentitySignedQuotientSource block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr (Nat.card block.Points)
      (degreeThreeKernelZeroTopAction block P)
      (degreeThreeKernelZeroTopAction_injective block P hK) (by
        rw [hs]
        norm_num)
  have hcap := degreeThree_translation_capacity_fourBlocks block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hs
  have hrate0 : 0 ≤ Real.logb 2 3 / 3 :=
    div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hcost : Real.logb 2 3 / 3 * H.capacity ≤
      Real.logb 2 3 / 3 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hcap hrate0
  have hlog : Real.logb 2 3 ≤ 8 / 5 := by
    have hp : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ)) hp
    simp only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2 (by
      simpa only [mul_comm] using le_of_lt h)
  have hw12 : w = 12 := by
    simpa only [hr, hs] using width_eq block
  have hwR : (w : ℝ) = 12 := by exact_mod_cast hw12
  have hsR : (Nat.card block.Points : ℝ) = 4 := by exact_mod_cast hs
  have heven : evenWidth w = 12 := by
    rw [hw12]
    norm_num [evenWidth, halfDegree]
  rw [hwR, heven, hsR]
  norm_num [preE7CharacterRho]
  linarith

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
