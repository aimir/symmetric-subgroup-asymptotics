import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DiagramRootOrthogonality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicHeightLayer

/-! The E6 diagram involution acts on the ACTUAL exact-height root
indices and gives literal isomorphisms of their root lines. Their positive
group inclusions intertwine the actual matrix twist definitionally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightRootPermutation
open CFSGTwistedE6GeckRootSubgroupTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6DiagramRootOrthogonality
open CFSGTwistedE6WeylChamber CFSGNormTwoRootPairing CFSGNormTwoCartanDiagramWords
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateIntrinsicHeightLayer CFSGSerreDiagram CFSGIntegerHeightSign

abbrev HeightIndex (h : ℤ) := ExactHeightRoot CartanMatrix.E₆ h

theorem diagramRoot_involutive (k : Roots CartanMatrix.E₆) : diagramRoot (diagramRoot k)=k := by
  apply Subtype.ext
  funext i
  rw [diagramRoot_coordinate,diagramRoot_coordinate,diagramPermutation_involutive]

def heightRootMap (h : ℤ) (k : HeightIndex h) : HeightIndex h :=
  ⟨⟨diagramRoot k.val.val,by
    intro i
    rw [diagramRoot_coordinate]
    exact k.val.property _⟩,by
      change height (diagramRoot k.val.val).val=h
      rw [rootPermutation_height]
      exact k.property⟩

theorem heightRootMap_involutive (h : ℤ) (k : HeightIndex h) :
    heightRootMap h (heightRootMap h k)=k := by
  apply Subtype.ext
  apply Subtype.ext
  exact diagramRoot_involutive k.val.val

def heightRootPermutation (h : ℤ) : Equiv.Perm (HeightIndex h) where
  toFun:=heightRootMap h
  invFun:=heightRootMap h
  left_inv:=heightRootMap_involutive h
  right_inv:=heightRootMap_involutive h

def rootLineTwist (K : Type) [Field K] (sigma : K≃+*K) (h : ℤ) (k : HeightIndex h) :
    rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val≃*
    rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (heightRootPermutation h k).val.val :=
  ((unitTwist K sigma).subgroupMap _).trans (MulEquiv.subgroupCongr (root_subgroup_twist K sigma k.val.val))

theorem rootLineTwist_val (K : Type) [Field K] (sigma : K≃+*K) (h : ℤ)
    (k : HeightIndex h) (x : rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val) :
    (rootLineTwist K sigma h k x).val=unitTwist K sigma x.val := rfl

theorem rootLineInclusion_twist (K : Type) [Field K] (sigma : K≃+*K) (h : ℤ)
    (k : HeightIndex h) (x : rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val) :
    positiveTwist K sigma
      (rootLineInclusion CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val k.val.property x)=
      rootLineInclusion CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (heightRootPermutation h k).val.val
        (heightRootPermutation h k).val.property (rootLineTwist K sigma h k x) := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightRootPermutation
