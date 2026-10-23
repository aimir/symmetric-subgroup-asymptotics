import SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerRootPilot
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveSections
import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCentralizerCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicHeightLayer

/-! Literal positive root-orbit factors in the highest-root centralizer.
The centralization assertion is first proved in the actual E6 root-line
group. The folded F4 membership is then supplied by the checked actual
singleton/paired sections, not by a presumed fixed-group identification.
Cardinality and independence of products are separate conclusions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerOrbitFactors
open CFSGFFourE6CentralizerRootPilot CFSGFFourE6PositiveSections
open CFSGFFourE6DiagramFixed CFSGFFourSerreMatrices
open CFSGTwistedE6GeckSectionRootParameters CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckRootSubgroupTwist CFSGTwistedE6WeylChamber
open CFSGTwistedE6DiagramRootOrthogonality CFSGTwistedE6GeckMatrixTwist
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateIntrinsicHeightLayer
open CFSGNormTwoCoordinateRootCentralizerCardinality CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootPairCommute CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGSerreQuadraticMatrix

local instance rootDecEq : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) :=
  Classical.decEq _

abbrev highestRootLine (K : Type) [Field K] :
    Subgroup ((Matrix CFSGTwistedE6GeckDiagramCovariance.GeckIndex
      CFSGTwistedE6GeckDiagramCovariance.GeckIndex K)ˣ) := RootLine K highestRoot

def centralizingUpper (K : Type) [Field K] : Subgroup (Positive K) :=
  positiveRootCentralizer CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K highestRoot

def intervalPositive (K : Type) [Field K] (i : Fin 15) :
    RootLine K (intervalRoot i).val →* Positive K :=
  rootLineInclusion CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
    (intervalRoot i).val (intervalRoot i).property

theorem intervalPositive_val (K : Type) [Field K] (i : Fin 15)
    (x : RootLine K (intervalRoot i).val) :
    (intervalPositive K i x).val=rawRootUnit K (intervalRoot i) x := rfl

theorem interval_line_centralizes_highest (K : Type) [Field K] (i : Fin 15)
    (x : RootLine K (intervalRoot i).val) :
    intervalPositive K i x∈centralizingUpper K := by
  let a := (rootParameterEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K (intervalRoot i).val).symm x
  have ha := rootParameterEquiv_symm_val CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
      (intervalRoot i).val x
  have h := root_parameter_mem_centralizer CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
      highestRoot (intervalRoot i) (Or.inl (intervalRoot_orthogonal_highest i)) a
  have he : CFSGNormTwoCoordinateRootHeightQuotient.positiveRootParameterHom
      CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
        CartanMatrix.E₆_off_diag_nonpos K (intervalRoot i).val (intervalRoot i).property a =
      intervalPositive K i x := by
    apply Subtype.ext
    exact ha
  rw [he] at h
  exact h

theorem twisted_interval_centralizes_highest (K : Type) [Field K]
    (sigma : K≃+*K) (i : Fin 15) (x : RootLine K (intervalRoot i).val) :
    positiveTwist K sigma (intervalPositive K i x)∈centralizingUpper K := by
  have hm : unitTwist K sigma x.val∈RootLine K (diagramRoot (intervalRoot i).val) := by
    have h : unitTwist K sigma x.val∈
        (RootLine K (intervalRoot i).val).map (unitTwist K sigma).toMonoidHom :=
      ⟨x.val,x.property,rfl⟩
    rw [root_subgroup_twist] at h
    exact h
  rw [intervalRoot_diagram] at hm
  have h := interval_line_centralizes_highest K (partner i) ⟨unitTwist K sigma x.val,hm⟩
  change unitTwist K sigma x.val∈Subgroup.centralizer (highestRootLine K : Set _) at h ⊢
  exact h

def orbitFactor (K : Type) [Field K] (i : Fin 15)
    (x : RootLine K (intervalRoot i).val) : Positive K :=
  if partner i=i then intervalPositive K i x else
    intervalPositive K i x*positiveTwist K (RingEquiv.refl K) (intervalPositive K i x)

theorem orbitFactor_centralizes_highest (K : Type) [Field K] (i : Fin 15)
    (x : RootLine K (intervalRoot i).val) : orbitFactor K i x∈centralizingUpper K := by
  unfold orbitFactor
  split_ifs
  · exact interval_line_centralizes_highest K i x
  · exact (centralizingUpper K).mul_mem (interval_line_centralizes_highest K i x)
      (twisted_interval_centralizes_highest K (RingEquiv.refl K) i x)

theorem orbitFactor_mem_folded (K : Type) [Field K] [Finite K] (i : Fin 15)
    (x : RootLine K (intervalRoot i).val) :
    (orbitFactor K i x).val∈canonicalElementaryGroup realizationData K := by
  unfold orbitFactor
  split_ifs with hi
  · rw [intervalPositive_val,rawRootUnit_eq]
    apply singleton_root_mem_folded K (intervalRoot i) _ x
    rw [intervalRoot_diagram,hi]
  · have hne : diagramRoot (intervalRoot i).val≠(intervalRoot i).val := by
      intro he
      have hp : intervalRoot (partner i)=intervalRoot i := Subtype.ext
        ((intervalRoot_diagram i).symm.trans he)
      exact hi (intervalRoot_injective hp)
    change (intervalPositive K i x).val *
      unitTwist K (RingEquiv.refl K) (intervalPositive K i x).val∈_
    rw [intervalPositive_val]
    exact paired_root_mem_folded K (intervalRoot i) hne x

theorem orbitFactor_fixed (K : Type) [Field K] [Finite K] (i : Fin 15)
    (x : RootLine K (intervalRoot i).val) :
    positiveTwist K (RingEquiv.refl K) (orbitFactor K i x)=orbitFactor K i x := by
  apply Subtype.ext
  exact foldedModel_le_diagramFixed K (orbitFactor_mem_folded K i x)

end SymmetricSubgroupAsymptotics.CFSGFFourE6CentralizerOrbitFactors
