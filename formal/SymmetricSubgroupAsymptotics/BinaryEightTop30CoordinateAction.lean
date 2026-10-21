import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T30
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

/-! The original8T30 top acts on the same eight binary coordinates.
Only the already checked reversible spaces are reused; invariance is
checked against this original top's own three generators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop30CoordinateAction
abbrev H := Subgroup.closure (Set.range BinaryMenuCayley8T30.generators)
abbrev V := Fin 8 → ZMod 2
def generators : Fin 3 → H := closureGenerators BinaryMenuCayley8T30.generators
theorem generators_full : Subgroup.closure (Set.range generators) = ⊤ :=
  closureGenerators_full _
def rho : Representation (ZMod 2) H V :=
  (binaryPermutationRepresentation 8).comp H.subtype
def word (w : List (Fin 3)) : H := (w.map generators).prod
end SymmetricSubgroupAsymptotics.BinaryEightTop30CoordinateAction
