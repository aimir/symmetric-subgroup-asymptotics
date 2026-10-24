import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
import SymmetricSubgroupAsymptotics.ElementaryInducedOrdinaryGeneratorStep
import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof

/-! Ordinary generation across an actual elementary local-chief step.
The original correlated kernel inclusion is CONSTRUCTED by the existing
orbit-evaluation map. The capacity is the proved least induced capacity;
no module-capacity or ordinary-generator INPUT is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathElementaryOrdinaryStep

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] [Finite D']
    (phi : S.D →* D') (C : ElementaryMinimalNormalChart phi.ker)

def layerCapacity (i : I) : ℕ :=
  InducedMinimumUniformCapacity.capacity (S.topPointStabilizer i)
    (ActualWreathAffineCapacity.localRepresentation S phi C i)

theorem genRank_le_capacity_add_quotient (i : I) :
    MarkedC4.genRank S.A ≤ layerCapacity S phi C i +
      MarkedC4.genRank (S.A ⧸ PermutationalWreathProduct.Compression.kernel S.rho phi) := by
  have hu : UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.ambientRepresentation S phi C)
      (layerCapacity S phi C i) :=
    (InducedMinimumUniformCapacity.uniform (S.topPointStabilizer i)
      (ActualWreathAffineCapacity.localRepresentation S phi C i)).of_injective
        (ActualWreathAffineCapacity.inducedIntertwiner S phi C i)
        (ActualWreathAffineCapacity.inducedIntertwiner_injective S phi C i)
  have hq : UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.E S phi C).quotientRepresentation.ρ
      (layerCapacity S phi C i) :=
    UniformSubrepresentationGeneratorBound.of_comp
      (ActualWreathAffineCapacity.E S phi C).quotientRepresentation.ρ
      (QuotientGroup.mk' (ActualWreathAffineCapacity.K S phi)) hu
  have h := ElementaryInducedOrdinaryGeneratorStep.genRank_le_of_uniform
    (ActualWreathAffineCapacity.K S phi) (ActualWreathAffineCapacity.E S phi C)
    (layerCapacity S phi C i) hq
  exact h.trans_eq (Nat.add_comm _ _)

/-- The next ambient group is the actual compressed quotient, with the
same original top and block set, not an abstract extension model. -/
theorem genRank_le_capacity_add_next (hphi : Function.Surjective phi) (i : I) :
    MarkedC4.genRank S.A ≤ layerCapacity S phi C i +
      MarkedC4.genRank (S.quotient D' phi hphi).A :=
  genRank_le_capacity_add_quotient S phi C i

omit [Finite D'] in
theorem layerCapacity_le_half (i : I) (hI : 2 ≤ Fintype.card I) :
    (layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ) * Fintype.card I / 2 := by
  have hi : 2 ≤ (S.topPointStabilizer i).index := by
    simpa only [S.topPointStabilizer_index i] using hI
  simpa only [layerCapacity, S.topPointStabilizer_index i] using
    InducedMinimumUniformCapacity.half (S.topPointStabilizer i)
      (ActualWreathAffineCapacity.localRepresentation S phi C i) hi

omit [Finite D'] in
theorem layerCapacity_le_log (i : I) (hI : 2 ≤ Fintype.card I) :
    (layerCapacity S phi C i : ℝ) ≤
      traceyInducedGeneratorCeiling (Module.finrank (ZMod C.p) C.V) (Fintype.card I) := by
  have hi : 2 ≤ (S.topPointStabilizer i).index := by
    simpa only [S.topPointStabilizer_index i] using hI
  simpa only [layerCapacity, S.topPointStabilizer_index i] using
    InducedMinimumUniformCapacity.logarithmic (S.topPointStabilizer i)
      (ActualWreathAffineCapacity.localRepresentation S phi C i) hi

end SymmetricSubgroupAsymptotics.ActualWreathElementaryOrdinaryStep
