import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairNormalStateQuotients
import Mathlib.Tactic.FinCases

/-!
# Action 023 one-general pilot: named normal states

This is the light front end of the split action-023 pilot.  It proves only
the bottom and top normal-state equations.  The failed monolithic pilot is
retained separately as recovery evidence.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit

open Non2UnipotentPrefixFiniteMenu

abbrev Original :=
  PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.Original

def stateZero :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalCount :=
  ⟨0, by change 0 < 3; norm_num⟩

def stateMiddle :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalCount :=
  ⟨1, by change 1 < 3; norm_num⟩

def stateTop :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalCount :=
  ⟨2, by change 2 < 3; norm_num⟩

def genZero :
    Fin degreeTwoSixPairAction023CheckedLiteral.normalGeneratorWidth :=
  ⟨0, by change 0 < 3; norm_num⟩

theorem stateZero_eq_bot :
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateZero).1 =
      ⊥ := by
  change Subgroup.closure
    (Set.range
      (PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 0)) = ⊥
  exact
    PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.normalRegistry.bottom_eq

private theorem stateTop_generator (j : Fin 3) :
    degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateTop j =
      PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.ambient j := by
  fin_cases j
  · change PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 2 0 =
      PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.ambient 0
    exact congrArg
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
      (by native_decide)
  · change PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 2 1 =
      PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.ambient 1
    exact congrArg
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
      (by native_decide)
  · change PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.stateGenerators 2 2 =
      PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.ambient 2
    exact congrArg
      PrimitiveAffineDegreeTwoSixPairAction023ClassPilot.originalEquiv
      (by native_decide)

private theorem stateTop_generator_range :
    Set.range
        (degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateTop) =
      Set.range
        PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.ambient := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, (stateTop_generator j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, stateTop_generator j⟩

theorem stateTop_eq_top :
    (degreeTwoSixPairAction023CheckedLiteral.normalStateIndex stateTop).1 =
      ⊤ := by
  change Subgroup.closure
    (Set.range
      (degreeTwoSixPairAction023CheckedLiteral.stateGenerators stateTop)) = ⊤
  rw [stateTop_generator_range]
  exact
    PrimitiveAffineDegreeTwoSixPairAction023CatalogueRow.normalRegistry.ambient_full

end PrimitiveAffineDegreeTwoSixPairAction023OneGeneralSplit
end SymmetricSubgroupAsymptotics

end
