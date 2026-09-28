import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixPhysicalForwardEstimate
import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixResidualClosure

/-!
# Exact outside-frontier split at the E7 alphabet boundary

The post-alphabet outside sector consists of literal outside-`Fits` subgroups
whose every orbit already lies in the binary/natural-`S3`/selected-UP
alphabet.  Residual closure proves that every such subgroup is accepted by
the physical E7 owner, whose complete forward estimate is now available.

The complementary sector records exactly the still missing pre-E7 alphabet
reduction.  The split is an exact cardinal identity, so later earlier-owner
estimates can be added without overlap or duplicate E7 payment.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-- Outside subgroups for which the post-E7 orbitwise alphabet has already
been established. -/
abbrev PostE7CoveredOutsideFamily (n : ℕ) :=
  {H : OutsideFitsSubgroupSetAt n // UPResidualOrbitCovered H.1}

/-- The exact complementary outside sector.  Closing it requires the
historical earlier-owner/alphabet reduction, not another E7 estimate. -/
abbrev PreE7UnresolvedOutsideFamily (n : ℕ) :=
  {H : OutsideFitsSubgroupSetAt n // ¬ UPResidualOrbitCovered H.1}

/-- The outside frontier partitions literally at the orbitwise alphabet
boundary. -/
def outsideFitsE7AlphabetPartitionEquiv (n : ℕ) :
    OutsideFitsSubgroupSetAt n ≃
      PostE7CoveredOutsideFamily n ⊕ PreE7UnresolvedOutsideFamily n :=
  (Equiv.sumCompl
    (fun H : OutsideFitsSubgroupSetAt n => UPResidualOrbitCovered H.1)).symm

def postE7CoveredOutsideRatio (n : ℕ) : ℝ :=
  (Nat.card (PostE7CoveredOutsideFamily n) : ℝ) / exactBenchmark n

def preE7UnresolvedOutsideRatio (n : ℕ) : ℝ :=
  (Nat.card (PreE7UnresolvedOutsideFamily n) : ℝ) / exactBenchmark n

/-- Exact normalized decomposition of the complete outside frontier. -/
theorem outsideFitsAtRatio_eq_e7Alphabet_partition (n : ℕ) :
    outsideFitsAtRatio n =
      postE7CoveredOutsideRatio n + preE7UnresolvedOutsideRatio n := by
  have hcard : Nat.card (OutsideFitsSubgroupSetAt n) =
      Nat.card (PostE7CoveredOutsideFamily n) +
        Nat.card (PreE7UnresolvedOutsideFamily n) := by
    rw [Nat.card_congr (outsideFitsE7AlphabetPartitionEquiv n), Nat.card_sum]
  unfold outsideFitsAtRatio postE7CoveredOutsideRatio
    preE7UnresolvedOutsideRatio
  rw [hcard, Nat.cast_add, add_div]

/-- Post-alphabet outside subgroups inject unchanged into the literal E7
owner union. -/
def postE7CoveredOutsideEmbedding
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) :
    PostE7CoveredOutsideFamily n ↪
      E7UPOwnedPhysical hTracey hExceptional n where
  toFun H :=
    ⟨H.1.1, e7UPPhysicalOwnerMenu_covers_outside
      hTracey hExceptional H.1.1 H.1.2 H.2⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun X : E7UPOwnedPhysical hTracey hExceptional n => X.1) h

/-- The post-alphabet outside ratio is bounded by the already paid physical
E7 owner ratio. -/
theorem postE7CoveredOutsideRatio_le_e7UPOwned
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) :
    postE7CoveredOutsideRatio n ≤
      e7UPOwnedPhysicalRatio hTracey hExceptional n := by
  have hcard : Nat.card (PostE7CoveredOutsideFamily n) ≤
      Nat.card (E7UPOwnedPhysical hTracey hExceptional n) :=
    Nat.card_le_card_of_injective
      (postE7CoveredOutsideEmbedding hTracey hExceptional n)
      (postE7CoveredOutsideEmbedding hTracey hExceptional n).injective
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard)
    (exactBenchmark_pos n).le

/-- Complete forward estimate for the entire post-alphabet outside sector.
No second E7 scalar or row is introduced. -/
noncomputable def postE7CoveredOutside_exponentialForwardEstimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      postE7CoveredOutsideRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (e7UPOwnedPhysical_exponentialForwardEstimate hTracey hExceptional) 0
    (fun n _ => postE7CoveredOutsideRatio_le_e7UPOwned
      hTracey hExceptional n)

/-- The full outside-frontier producer now needs exactly one remaining
estimate: the complementary pre-E7 sector.  The post-alphabet E7 sector is
inserted here without duplicate payment. -/
noncomputable def outsideFrontier_exponentialForwardEstimate_of_preE7
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7UnresolvedOutsideRatio) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      OrdinaryFrontierClosure.outsideFrontierRatio := by
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    (postE7CoveredOutside_exponentialForwardEstimate hTracey hExceptional) P
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => by
      rw [outsideFrontierRatio_eq_outsideFitsAtRatio,
        outsideFitsAtRatio_eq_e7Alphabet_partition])

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
