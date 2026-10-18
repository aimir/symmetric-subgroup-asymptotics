import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixNormalComparatorSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathGroup

/-!
# The degree-six `S₃ ≀ C₂` affine cell

Coordinatewise sign on the two `S₃` factors, together with the unchanged
block swap, gives an onto map

`S₃ ≀ C₂ → C₂ ≀ C₂ = D₈`.

Its kernel is `A₃²`.  It is contained in every nontrivial normal subgroup,
so the nonbottom axes use the faithful degree-four action of `D₈`.  The
bottom axis uses the ternary cyclic dual on the second derived subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Wreath

/-- The two exact finite group facts left after defining the sign quotient. -/
structure Algebra : Type where
  target : DerivedHead.DerivedCyclicTarget G projection.ker 1 3
  normal_cover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → projection.ker ≤ N

theorem automorphism_card_le : Nat.card (G ≃* G) ≤ 2 ^ 216 := by
  calc
    Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.log 2 (Nat.card G) :=
      Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log G
    _ = 72 ^ 6 := by rw [card_G]; norm_num
    _ ≤ 2 ^ 216 := by norm_num

end DegreeSixS3Wreath

namespace Non2UnipotentPrefixFiniteMenu

/-- Recognition data for the literal retained wreath action. -/
structure PreE7DegreeSixS3WreathSource
    (U : PreE7NonPairActionClass 6) : Type where
  equiv : preE7NonPairAction 6 U ≃* DegreeSixS3Wreath.G

namespace PreE7DegreeSixS3WreathSource

variable {U : PreE7NonPairActionClass 6}
  (S : PreE7DegreeSixS3WreathSource U)
  (A : DegreeSixS3Wreath.Algebra)

/-- The exact normal-comparator model with `D₈` comparator. -/
def model : PreE7NormalComparatorModel 6 U where
  G := DegreeSixS3Wreath.G
  equiv := S.equiv
  index := Unit
  R := DegreeSixS3Wreath.D8
  degree := 4
  action := DegreeSixS3Wreath.d8Action
  action_injective := DegreeSixS3Wreath.d8Action_injective
  proj := fun _ => DegreeSixS3Wreath.projection
  proj_surjective := fun _ => DegreeSixS3Wreath.projection_surjective
  normal_cover := fun N hN hNb => ⟨(), A.normal_cover N hN hNb⟩
  tailSlope := Real.logb 2 3 / 3
  tailConstant := Nat.card
    (DegreeSixS3Wreath.G ≃* DegreeSixS3Wreath.G)
  tailConstant_nonneg := by positivity
  tail := fun _ J => A.target.epi_card_le_ternary J
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := logThreeThird_le_window (by norm_num)

private theorem tailConstant_le :
    (S.model A).tailConstant ≤ (2 : ℝ) ^ (36 * (6 : ℝ)) := by
  change (Nat.card (DegreeSixS3Wreath.G ≃* DegreeSixS3Wreath.G) : ℝ) ≤ _
  calc
    (Nat.card (DegreeSixS3Wreath.G ≃* DegreeSixS3Wreath.G) : ℝ) ≤
        ((2 ^ 216 : ℕ) : ℝ) := by
      exact_mod_cast DegreeSixS3Wreath.automorphism_card_le
    _ = (2 : ℝ) ^ (36 * (6 : ℝ)) := by norm_num

/-- Completed degree-six source for the full wreath cell. -/
noncomputable def source : PreE7RankTailSourceOrYonedaTopData 6 U :=
  DegreeSixNormalComparatorSource.source (S.model A) (S.tailConstant_le A)

end PreE7DegreeSixS3WreathSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
