import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSections
import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicHeightLayer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCentralizerCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightRootPermutation

/-! Actual folded-positive factors at ARBITRARY positive E6 roots.
This is the transported version of the selected interval pilot: a fixed
root contributes one root-line factor and a nonfixed root contributes
the literal product with its diagram partner. Orthogonality to a target
root is checked on BOTH orbit members before centralization is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveOrbitFactors
open CFSGFFourE6PositiveSections CFSGFFourE6DiagramFixed CFSGFFourSerreMatrices
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckRootSubgroupTwist CFSGTwistedE6WeylChamber
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateIntrinsicHeightLayer
open CFSGNormTwoCoordinateRootCentralizerCardinality CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootPairCommute CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGIntegerMatrixPairing
open CFSGSerreQuadraticMatrix

local instance rootDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

abbrev rootLineAt (K : Type) [Field K] (a : Roots CartanMatrix.E₆) :
    Subgroup ((Matrix GeckIndex GeckIndex K)ˣ) := RootLine K a

def rootCentralizer (K : Type) [Field K] (a : Roots CartanMatrix.E₆) : Subgroup (Positive K) :=
  positiveRootCentralizer CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K a

def positiveInclusion (K : Type) [Field K]
    (k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot) : RootLine K k.val→*Positive K :=
  rootLineInclusion CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val k.property

theorem positiveInclusion_val (K : Type) [Field K]
    (k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot) (x : RootLine K k.val) :
    (positiveInclusion K k x).val=rawRootUnit K k x := rfl

def rootOrbitFactor (K : Type) [Field K]
    (k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot) (x : RootLine K k.val) : Positive K :=
  if diagramRoot k.val=k.val then positiveInclusion K k x else
    positiveInclusion K k x*positiveTwist K (RingEquiv.refl K) (positiveInclusion K k x)

theorem rootOrbitFactor_mem_folded (K : Type) [Field K] [Finite K]
    (k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot) (x : RootLine K k.val) :
    (rootOrbitFactor K k x).val∈canonicalElementaryGroup realizationData K := by
  unfold rootOrbitFactor
  split_ifs with hk
  · rw [positiveInclusion_val,rawRootUnit_eq]
    exact singleton_root_mem_folded K k hk x
  · change (positiveInclusion K k x).val*
      unitTwist K (RingEquiv.refl K) (positiveInclusion K k x).val∈_
    rw [positiveInclusion_val]
    exact paired_root_mem_folded K k hk x

theorem rootOrbitFactor_fixed (K : Type) [Field K] [Finite K]
    (k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot) (x : RootLine K k.val) :
    positiveTwist K (RingEquiv.refl K) (rootOrbitFactor K k x)=rootOrbitFactor K k x := by
  apply Subtype.ext
  exact foldedModel_le_diagramFixed K (rootOrbitFactor_mem_folded K k x)

theorem positiveInclusion_centralizes (K : Type) [Field K]
    (k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot) (a : Roots CartanMatrix.E₆)
    (hpair : integerPairing CartanMatrix.E₆ k.val.val a.val=0) (x : RootLine K k.val) :
    positiveInclusion K k x∈rootCentralizer K a := by
  let t := (rootParameterEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val).symm x
  have ht := rootParameterEquiv_symm_val CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val x
  have h := root_parameter_mem_centralizer CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K a k
      (Or.inl hpair) t
  have he : CFSGNormTwoCoordinateRootHeightQuotient.positiveRootParameterHom
      CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
        CartanMatrix.E₆_off_diag_nonpos K k.val k.property t=positiveInclusion K k x := by
    apply Subtype.ext
    exact ht
  rw [he] at h
  exact h

theorem rootOrbitFactor_centralizes (K : Type) [Field K]
    (k : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot) (a : Roots CartanMatrix.E₆)
    (hpair : integerPairing CartanMatrix.E₆ k.val.val a.val=0)
    (hpartner : integerPairing CartanMatrix.E₆ (diagramRoot k.val).val a.val=0)
    (x : RootLine K k.val) : rootOrbitFactor K k x∈rootCentralizer K a := by
  have hm : unitTwist K (RingEquiv.refl K) x.val∈RootLine K (diagramRoot k.val) := by
    have h : unitTwist K (RingEquiv.refl K) x.val∈
        (RootLine K k.val).map (unitTwist K (RingEquiv.refl K)).toMonoidHom :=
      ⟨x.val,x.property,rfl⟩
    rw [root_subgroup_twist] at h
    exact h
  let kp : CFSGTwistedE6GeckOriginalRootSections.PositiveRoot := ⟨diagramRoot k.val,by
    intro i
    rw [CFSGTwistedE6DiagramRootOrthogonality.diagramRoot_coordinate]
    exact k.property _⟩
  have ht := positiveInclusion_centralizes K kp a hpartner
    ⟨unitTwist K (RingEquiv.refl K) x.val,hm⟩
  change unitTwist K (RingEquiv.refl K) x.val∈Subgroup.centralizer (rootLineAt K a : Set _) at ht
  unfold rootOrbitFactor
  split_ifs
  · exact positiveInclusion_centralizes K k a hpair x
  · apply (rootCentralizer K a).mul_mem (positiveInclusion_centralizes K k a hpair x)
    change unitTwist K (RingEquiv.refl K) x.val∈Subgroup.centralizer (rootLineAt K a : Set _)
    exact ht

end SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveOrbitFactors
