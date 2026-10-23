import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramFieldRootTwist

/-! The actual E6 diagram--field twist transports every integral root
line, using the generic word-witness theorem for the SAME raw datum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootSubgroupTwist
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist CFSGSerreDiagram
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCartanDiagramRoots
open CFSGSerreQuadraticWeylWord

theorem unitTwist_word (K : Type) [CommRing K] (sigma : K≃+*K) (w : List (Fin 6)) :
    unitTwist K sigma (canonicalWord rawData K w)=canonicalWord rawData K (w.map e6Permutation) :=
  CFSGNormTwoCoordinateDiagramFieldRootTwist.unitTwist_word CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    e6Permutation e6_preserves K sigma w

theorem root_subgroup_twist (K : Type) [Field K] (sigma : K≃+*K) (k : Roots CartanMatrix.E₆) :
    (rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k).map (unitTwist K sigma).toMonoidHom=
      rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
        (rootPermutation CartanMatrix.E₆ e6Permutation e6_preserves k) :=
  CFSGNormTwoCoordinateDiagramFieldRootTwist.root_subgroup_twist CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    e6Permutation e6_preserves K sigma k

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootSubgroupTwist
