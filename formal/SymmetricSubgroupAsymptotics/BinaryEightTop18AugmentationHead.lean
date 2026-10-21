import SymmetricSubgroupAsymptotics.BinaryCoordinateInvariantFunctionalCertificate
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T18

/-! One selected augmentation-head certificate for the SAME original8T18
action. Only128 seven-coordinate binary functionals are considered. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop18AugmentationHead
abbrev H := Subgroup.closure (Set.range BinaryMenuCayley8T18.generators)
def rho : Representation (ZMod 2) H (Fin 8 → ZMod 2) :=
  (binaryPermutationRepresentation 8).comp H.subtype
def generators : Fin 5 → H := closureGenerators BinaryMenuCayley8T18.generators

private theorem selected_certificate : ∃ j : Fin 7, ∀ t : Fin 7 → ZMod 2,
    BinaryCoordinateInvariantFunctionalCertificate.Compatible rho generators
      BinaryRegularEightNaturalRegistry.chart45 t → t j = 0 → t = 0 := by
  unfold BinaryCoordinateInvariantFunctionalCertificate.Compatible
  decide +kernel

theorem head_le_one (W : Subrepresentation rho)
    (hW : W.toSubmodule = BinaryRegularEightNaturalRegistry.chart45.space) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 1 := by
  obtain ⟨j, hj⟩ := selected_certificate
  exact BinaryCoordinateInvariantFunctionalCertificate.head_finrank_le_one
    rho generators BinaryRegularEightNaturalRegistry.chart45 W hW j hj

end SymmetricSubgroupAsymptotics.BinaryEightTop18AugmentationHead
