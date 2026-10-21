import SymmetricSubgroupAsymptotics.BinaryRegularSixCanonicalGenerators
import SymmetricSubgroupAsymptotics.BinaryPairFrameConjugateTop

/-! Canonical reindexing of an outer pair frame keeps the same physical
source while identifying its actual top with the six original rows. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem canonical_regular_top_range
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace = BinaryRegularSixCanonicalGenerators.K.space) :
    (F.reindex E.canonicalPointLabels).top.range =
      Subgroup.closure (Set.range BinaryRegularSixCanonicalGenerators.generators) := by
  rw [F.reindex_top_range]
  exact BinaryRegularSixCanonicalGenerators.BinaryPairFrame.canonical_regular_six_closure
    E hzero hH hK

end SymmetricSubgroupAsymptotics.BinaryPairFrame
