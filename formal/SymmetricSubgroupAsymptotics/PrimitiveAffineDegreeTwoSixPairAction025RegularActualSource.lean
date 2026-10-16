import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025LightPhysical
import SymmetricSubgroupAsymptotics.CubicActualRepresentativeSource

/-! A genuine source-table-ready action25 row through the import-light
actual regular C3 subgroup route. No48row object or normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineDegreeTwoSixPairAction025RegularActualSource
open PrimitiveAffineDegreeTwoSixPairAction025RegularPilot
open PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal
open LinearSemidirectSubgroupKernelChart
open BinaryThreeQuartetCubicImageSocles (linear)

theorem exists_source (hKP : KovacsPraegerAbelianizationBound) :
    ∃ p : PreE7PairActionClass 6, ∃ c : Equiv.Perm (Fin 12),
      relabelSubgroup c Original = preE7PairAction 6 p ∧
      Nonempty (PreE7B6SourceData 12 (preE7SixPairNonPairAction p)) :=
  CubicActualRepresentativeSource.exists_actualRepresentativeSource Original
    PrimitiveAffineDegreeTwoSixPairAction025LightPhysical.nonbinary
    PrimitiveAffineDegreeTwoSixPairAction025LightPhysical.transitive
    pairFrame originalEquiv (projection linear K) projection_surjective
    (CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective)
    (CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective)
    (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective)
    scalar_nonzero hKP

def representative (hKP : KovacsPraegerAbelianizationBound) : PreE7PairActionClass 6 :=
  Classical.choose (exists_source hKP)

def source (hKP : KovacsPraegerAbelianizationBound) :
    PreE7B6SourceData 12 (preE7SixPairNonPairAction (representative hKP)) :=
  Classical.choice (Classical.choose_spec (Classical.choose_spec (exists_source hKP))).2

theorem actual_correspondence (hKP : KovacsPraegerAbelianizationBound) :
    ∃ c : Equiv.Perm (Fin 12), relabelSubgroup c Original =
      preE7PairAction 6 (representative hKP) := by
  have h := Classical.choose_spec (exists_source hKP)
  exact ⟨Classical.choose h,(Classical.choose_spec h).1⟩

end PrimitiveAffineDegreeTwoSixPairAction025RegularActualSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
