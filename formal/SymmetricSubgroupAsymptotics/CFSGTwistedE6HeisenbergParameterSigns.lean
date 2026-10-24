import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergStableRootFamilies
import SymmetricSubgroupAsymptotics.CFSGSelectedRootDiagramParameterTwist

/-! Integral parameter signs on the SAME reoriented E6 Heisenberg roots.
The signs are chosen before the coefficient field, and the displayed
twist is the actual original Geck diagram--field matrix automorphism.
No fixed-coordinate cardinality or sign normalization is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergParameterSigns
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6WeylChamber CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGTwistedE6GeckMatrixTwist CFSGSerreDiagram
open CFSGNormTwoCoordinateSelectedRootElement CFSGSelectedRootDiagramParameterTwist

abbrev rootParameter (K : Type) [CommRing K] (k : Roots CartanMatrix.E₆) (a : K) :=
  selectedRootElement CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k a

def twistSign (k : Roots CartanMatrix.E₆) : ℤ :=
  (selectedRootElement_twist_sign CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    e6Permutation e6_preserves k).choose

theorem twistSign_unit (k : Roots CartanMatrix.E₆) :
    twistSign k = 1 ∨ twistSign k = -1 :=
  (selectedRootElement_twist_sign CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    e6Permutation e6_preserves k).choose_spec.1

theorem rootParameter_twist (K : Type) [CommRing K] (sigma : K ≃+* K)
    (k : Roots CartanMatrix.E₆) (a : K) :
    unitTwist K sigma (rootParameter K k a) =
      rootParameter K (diagramRoot k) ((twistSign k : K) * sigma a) :=
  (selectedRootElement_twist_sign CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    e6Permutation e6_preserves k).choose_spec.2 K sigma a

theorem firstParameter_twist (K : Type) [CommRing K] (sigma : K ≃+* K)
    (i : Fin 10) (a : K) :
    unitTwist K sigma (rootParameter K (configuration.xRoot i).val a) =
      rootParameter K (configuration.xRoot (partner i)).val
        ((twistSign (configuration.xRoot i).val : K) * sigma a) := by
  rw [rootParameter_twist, diagram_first]

theorem secondParameter_twist (K : Type) [CommRing K] (sigma : K ≃+* K)
    (i : Fin 10) (a : K) :
    unitTwist K sigma (rootParameter K (configuration.yRoot i).val a) =
      rootParameter K (configuration.yRoot (partner i)).val
        ((twistSign (configuration.yRoot i).val : K) * sigma a) := by
  rw [rootParameter_twist, diagram_second]

theorem centralParameter_twist (K : Type) [CommRing K] (sigma : K ≃+* K) (a : K) :
    unitTwist K sigma (rootParameter K configuration.zRoot.val a) =
      rootParameter K configuration.zRoot.val
        ((twistSign configuration.zRoot.val : K) * sigma a) := by
  rw [rootParameter_twist, diagram_central]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergParameterSigns
