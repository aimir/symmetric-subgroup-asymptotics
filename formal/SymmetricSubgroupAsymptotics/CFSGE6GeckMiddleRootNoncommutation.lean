import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleBracketDegrees
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSingleDegreeSpan
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutingFirstLayers
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveFirstLayer

/-! The paired/singleton middle edge is detected in every characteristic
by ONE literal lattice-degree projection. The two adjacent brackets have
different integral degrees, so characteristic two cannot cancel them. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootNoncommutation
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckRelativeRootGenerated
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckSimpleBracketDegrees CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoCoordinateHeight CFSGGradedMatrixSingleDegreeSpan
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixCommutingFirstLayers
open CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
private abbrev E (K : Type) [Field K] (i : Fin 6) : Matrix GeckIndex GeckIndex K :=
  fieldRoot rawData K false i
private abbrev ell := latticeWeight A hs hp E6Base
private abbrev degree (i j : Fin 6) := (E6Index i : CFSGNormTwoRootPairing.Roots A).val+
  (E6Index j : CFSGNormTwoRootPairing.Roots A).val
private abbrev w := weight A hs hp E6Base coordinateHeight

private theorem middle_degrees_ne : degree 2 3≠degree 4 3 := by
  intro he
  have h := congrFun he (2 : Fin 6)
  change ((Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6→ℤ) 2+(Pi.single (3 : Fin 6) (1 : ℤ) : Fin 6→ℤ) 2)=
    ((Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6→ℤ) 2+(Pi.single (3 : Fin 6) (1 : ℤ) : Fin 6→ℤ) 2) at h
  norm_num [Pi.single_apply,Fin.ext_iff] at h

theorem middle_bracket_ne_zero (K : Type) [Field K] : ⁅E K 2+E K 4,E K 3⁆≠0 := by
  intro hz
  have h : ⁅E K 2,E K 3⁆+⁅E K 4,E K 3⁆=0 := by simpa only [add_lie] using hz
  have hh := congrArg (degreePart ell (degree 2 3)) h
  rw [map_add,degreePart_eq ell (degree 2 3) _
    (simple_bracket_support A hs hp E6Base E6Index K 2 3),
    degreePart_zero_of_other ell (degree 2 3) (degree 4 3) _
      (simple_bracket_support A hs hp E6Base E6Index K 4 3) middle_degrees_ne,
    map_zero,add_zero] at hh
  exact (adjacent_bracket_ne_zero A hs hp E6Base E6Index K 2 3
    (by rw [E6_cartan];decide)) hh

private theorem firstLayer_simple (K : Type) [Field K] (i : Fin 6) :
    firstLayer w (canonicalRoot rawData K false i 1)=E K i := by
  simpa only [one_smul] using simple_firstLayer A hs hp E6Base E6Index coordinateHeight
    (simple_height A CartanMatrix.E₆_diag hs hp CartanMatrix.E₆_off_diag_nonpos) K i 1

theorem middle_parameter_not_commute (K : Type) [Field K] :
    ¬Commute (orbitParameter K false 1 1) (orbitParameter K false 2 1) := by
  intro hc
  have hheight := simple_height A CartanMatrix.E₆_diag hs hp CartanMatrix.E₆_off_diag_nonpos
  have hu := (positive_firstLayer_mem_span A hs hp E6Base E6Index coordinateHeight hheight K
    (orbitParameter K false 1 1) (orbitParameter_mem_upper K false 1 1)).1
  have hv := (positive_firstLayer_mem_span A hs hp E6Base E6Index coordinateHeight hheight K
    (orbitParameter K false 2 1) (orbitParameter_mem_upper K false 2 1)).1
  have hfirst : firstLayer w (orbitParameter K false 1 1)=E K 2+E K 4 := by
    change firstLayer w (canonicalRoot rawData K false 2 1*canonicalRoot rawData K false 4 1)=_
    rw [firstLayer_mul w _ _
      (simple_strict A hs hp E6Base E6Index coordinateHeight hheight K 2 1)
      (simple_strict A hs hp E6Base E6Index coordinateHeight hheight K 4 1),
      firstLayer_simple,firstLayer_simple]
  have hsecond : firstLayer w (orbitParameter K false 2 1)=E K 3 := firstLayer_simple K 3
  have hz := firstLayers_lie_eq_zero w _ _ hu hv hc
  rw [hfirst,hsecond] at hz
  exact middle_bracket_ne_zero K hz

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootNoncommutation
