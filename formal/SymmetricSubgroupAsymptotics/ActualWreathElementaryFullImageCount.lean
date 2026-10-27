import SymmetricSubgroupAsymptotics.ClosedInducedFullImageCount
import SymmetricSubgroupAsymptotics.ActualWreathElementaryOrdinaryStep

/-! An actual elementary local-chief compression counts all subgroups
onto the SAME compressed image. Its correlated module embedding is the
constructed orbit-evaluation map, not a new module-capacity premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathElementaryFullImageCount
open PermutationalWreathProduct

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]
    (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] [Finite D']
    (phi : S.D →* D') (C : ElementaryMinimalNormalChart phi.ker)

theorem card_fullImage_le_capacity_add_rank (i : I) :
    Nat.card (FiniteAbelianExtensionWholeLayerCount.FullImage
      (QuotientGroup.mk' (Compression.kernel S.rho phi))) ≤
      (Nat.card (ActualWreathAffineCapacity.E S phi C).quotientRepresentation)^
        (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i+
          MarkedC4.genRank (S.A ⧸ Compression.kernel S.rho phi)) := by
  exact ClosedInducedFullImageCount.card_fullImage_le_capacity_add_rank
    (p := C.p) (E := S.A) (B := S.A ⧸ Compression.kernel S.rho phi) (V := C.V)
    (QuotientGroup.mk' (Compression.kernel S.rho phi))
    (QuotientGroup.mk'_surjective _)
    (ActualWreathAffineCapacity.E S phi C).quotientRepresentation
    (ActualWreathAffineCapacity.E S phi C).originalKernelChart
    (S.topPointStabilizer i) (ActualWreathAffineCapacity.localRepresentation S phi C i)
    (ActualWreathAffineCapacity.inducedIntertwiner S phi C i)
    (ActualWreathAffineCapacity.inducedIntertwiner_injective S phi C i)

omit [Finite D'] in
theorem capacity_le_root_log (i : I) (hI : 2≤Fintype.card I) :
    (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ)≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*Fintype.card I /
        Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)) := by
  have hi : 2≤(S.topPointStabilizer i).index := by
    rw [S.topPointStabilizer_index]
    exact hI
  simpa only [ActualWreathElementaryOrdinaryStep.layerCapacity,
    S.topPointStabilizer_index] using
    InducedMinimumUnitLogarithmic.logarithmic_real (S.topPointStabilizer i)
      (ActualWreathAffineCapacity.localRepresentation S phi C i) hi

end SymmetricSubgroupAsymptotics.ActualWreathElementaryFullImageCount
