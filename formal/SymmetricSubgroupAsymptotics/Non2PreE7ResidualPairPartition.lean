import SymmetricSubgroupAsymptotics.Non2PreE7ResidualPairMenu
import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixOutsidePartition

/-!
# Remove the residual pair sector from the pre-E7 frontier

The exact pre-`E7` family is partitioned according to membership in the
closed four-width residual pair union.  The covered side embeds unchanged
into that physical union.  Consequently the only remaining pre-`E7`
estimate is the complementary non-pair residual; the pair row is paid once.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Pre-`E7` outside subgroups already covered by the residual pair menu. -/
abbrev PreE7ResidualPairCoveredFamily (n : ℕ) :=
  {H : PreE7UnresolvedOutsideFamily n //
    H.1.1 ∈ PreE7ResidualPairPhysical n}

/-- The exact pre-`E7` complement after removing all four residual pair
widths. -/
abbrev PreE7NonPairResidualFamily (n : ℕ) :=
  {H : PreE7UnresolvedOutsideFamily n //
    H.1.1 ∉ PreE7ResidualPairPhysical n}

/-- Literal partition of the pre-`E7` family at the residual-pair boundary. -/
def preE7ResidualPairPartitionEquiv (n : ℕ) :
    PreE7UnresolvedOutsideFamily n ≃
      PreE7ResidualPairCoveredFamily n ⊕
        PreE7NonPairResidualFamily n :=
  (Equiv.sumCompl
    (fun H : PreE7UnresolvedOutsideFamily n =>
      H.1.1 ∈ PreE7ResidualPairPhysical n)).symm

def preE7ResidualPairCoveredRatio (n : ℕ) : ℝ :=
  (Nat.card (PreE7ResidualPairCoveredFamily n) : ℝ) / exactBenchmark n

def preE7NonPairResidualRatio (n : ℕ) : ℝ :=
  (Nat.card (PreE7NonPairResidualFamily n) : ℝ) / exactBenchmark n

/-- Exact normalized decomposition after the residual pair removal. -/
theorem preE7UnresolvedOutsideRatio_eq_residualPair_partition (n : ℕ) :
    preE7UnresolvedOutsideRatio n =
      preE7ResidualPairCoveredRatio n + preE7NonPairResidualRatio n := by
  have hcard : Nat.card (PreE7UnresolvedOutsideFamily n) =
      Nat.card (PreE7ResidualPairCoveredFamily n) +
        Nat.card (PreE7NonPairResidualFamily n) := by
    rw [Nat.card_congr (preE7ResidualPairPartitionEquiv n), Nat.card_sum]
  unfold preE7UnresolvedOutsideRatio preE7ResidualPairCoveredRatio
    preE7NonPairResidualRatio
  rw [hcard, Nat.cast_add, add_div]

/-- Forgetting the outer pre-`E7` proof embeds the covered sector into the
already counted residual-pair physical union. -/
def preE7ResidualPairCoveredEmbedding (n : ℕ) :
    PreE7ResidualPairCoveredFamily n ↪ PreE7ResidualPairPhysical n where
  toFun H := ⟨H.1.1.1, H.2⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun X : PreE7ResidualPairPhysical n => X.1) h

theorem preE7ResidualPairCoveredRatio_le_physical (n : ℕ) :
    preE7ResidualPairCoveredRatio n ≤ preE7ResidualPairPhysicalRatio n := by
  have hcard : Nat.card (PreE7ResidualPairCoveredFamily n) ≤
      Nat.card (PreE7ResidualPairPhysical n) :=
    Nat.card_le_card_of_injective
      (preE7ResidualPairCoveredEmbedding n)
      (preE7ResidualPairCoveredEmbedding n).injective
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard)
    (exactBenchmark_pos n).le

/-- The covered side inherits the already closed residual-pair estimate. -/
noncomputable def preE7ResidualPairCovered_exponentialForwardEstimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7ResidualPairCoveredRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (preE7ResidualPairPhysical_exponentialForwardEstimate
      hTracey hExceptional) 0
    (fun n _ => preE7ResidualPairCoveredRatio_le_physical n)

/-- A forward estimate for the exact non-pair complement now closes the
whole pre-`E7` frontier. -/
noncomputable def preE7Unresolved_exponentialForwardEstimate_of_nonPair
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7UnresolvedOutsideRatio := by
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    (preE7ResidualPairCovered_exponentialForwardEstimate
      hTracey hExceptional) P
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => by
      rw [preE7UnresolvedOutsideRatio_eq_residualPair_partition])

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
