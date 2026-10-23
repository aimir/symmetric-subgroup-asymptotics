import SymmetricSubgroupAsymptotics.CFSGFFourE6RootSubgroups
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift

/-! The actual folded F4 matrices are fixed by the literal E6 diagram
involution with coefficient automorphism IDENTITY. Both signed simple
root formulas are checked; no fixed-group equality or source-image
faithfulness is asserted here. This is the positive-count pilot. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
open CFSGFFourSerreMatrices CFSGFFourE6RootSubgroups CFSGFFourE6PositiveRootUnits
open CFSGFFourE6NegativeRootUnits CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGSerreDiagram CFSGNormTwoGeckOrthogonalWeyl

private theorem folded_signed_root (K : Type) [Field K] (neg : Bool) (i : Fin 4) (t : K) :
    canonicalRoot realizationData K neg i t =
      ![canonicalRoot e6Data K neg 0 t * canonicalRoot e6Data K neg 5 t,
        canonicalRoot e6Data K neg 2 t * canonicalRoot e6Data K neg 4 t,
        canonicalRoot e6Data K neg 3 t,canonicalRoot e6Data K neg 1 t] i := by
  cases neg
  · exact folded_positive_root K i t
  · exact folded_negative_root K i t

theorem folded_root_fixed (K : Type) [Field K] (neg : Bool) (i : Fin 4) (t : K) :
    unitTwist K (RingEquiv.refl K) (canonicalRoot realizationData K neg i t) =
      canonicalRoot realizationData K neg i t := by
  have hr (j : Fin 6) : unitTwist K (RingEquiv.refl K) (canonicalRoot e6Data K neg j t) =
      canonicalRoot e6Data K neg (e6Permutation j) t :=
    unitTwist_root K (RingEquiv.refl K) neg j t
  rw [folded_signed_root]
  fin_cases i
  · change unitTwist K (RingEquiv.refl K)
      (canonicalRoot e6Data K neg 0 t * canonicalRoot e6Data K neg 5 t) =
      canonicalRoot e6Data K neg 0 t * canonicalRoot e6Data K neg 5 t
    rw [map_mul,hr,hr]
    change canonicalRoot e6Data K neg 5 t * canonicalRoot e6Data K neg 0 t =
      canonicalRoot e6Data K neg 0 t * canonicalRoot e6Data K neg 5 t
    exact (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K 0 5 (by rw [E6_cartan]; decide) neg neg t t).eq.symm
  · change unitTwist K (RingEquiv.refl K)
      (canonicalRoot e6Data K neg 2 t * canonicalRoot e6Data K neg 4 t) =
      canonicalRoot e6Data K neg 2 t * canonicalRoot e6Data K neg 4 t
    rw [map_mul,hr,hr]
    change canonicalRoot e6Data K neg 4 t * canonicalRoot e6Data K neg 2 t =
      canonicalRoot e6Data K neg 2 t * canonicalRoot e6Data K neg 4 t
    exact (orthogonal_signed_roots CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K 2 4 (by rw [E6_cartan]; decide) neg neg t t).eq.symm
  · exact hr 3
  · exact hr 1

def diagramFixed (K : Type) [Field K] : Subgroup ((Matrix Index Index K)ˣ) :=
  CFSGCentralTwistedCommutatorLift.fixedSubgroup (unitTwist K (RingEquiv.refl K))

theorem foldedModel_le_diagramFixed (K : Type) [Field K] :
    canonicalElementaryGroup realizationData K ≤ diagramFixed K := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg,i,t,rfl⟩
  exact folded_root_fixed K neg i t

theorem foldedRootGroup_le_diagramFixed (K : Type) [Field K] (neg : Bool) :
    foldedRootGroup K neg ≤ diagramFixed K :=
  (foldedRootGroup_le_model K neg).trans (foldedModel_le_diagramFixed K)

theorem folded_positive_le_fixedPositive (K : Type) [Field K] :
    foldedRootGroup K false ≤ Positive K ⊓ diagramFixed K :=
  le_inf (foldedRootGroup_le_ambient K false) (foldedRootGroup_le_diagramFixed K false)

end SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
