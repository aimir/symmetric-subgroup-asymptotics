import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeFunctionalIntersection

/-! Actual negative orbit-zero root groups and their complete fixed
singleton/paired charts. The reverse integral flag recovers the full
negative orbit group in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeOrbitRootGroups
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckOrbitRootIntersection
open CFSGE6GeckOrbitZeroRoots CFSGE6GeckSimpleOrbitFlags
open CFSGE6GeckFixedPairChart CFSGE6GeckFixedSimpleParameters
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckOrthogonalPairChart
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2
open CFSGNormTwoCoordinateNegativeFunctionalIntersection CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckHeightSupport CFSGSerreQuadraticMatrix
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆

def orbitNegativeGroup (K : Type) [Field K] (a : Fin 4) : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  (orbitPositiveGroup K a).map (rawOpposition K).toMonoidHom

private theorem simple_group_opposition (K : Type) [Field K] (i : Fin 6) :
    (canonicalRootSubgroup rawData K false i).map (rawOpposition K).toMonoidHom=
      canonicalRootSubgroup rawData K true i := by
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y,⟨a,rfl⟩,rfl⟩
    exact ⟨a,(rawSimple_opposition K false i (Multiplicative.ofAdd a)).symm⟩
  · rintro ⟨a,rfl⟩
    exact ⟨canonicalRoot rawData K false i a,⟨a,rfl⟩,
      rawSimple_opposition K false i (Multiplicative.ofAdd a)⟩

theorem orbitNegativeGroup_paired (K : Type) [Field K] (j : Fin 2) :
    orbitNegativeGroup K (pairedOrbit j)=canonicalRootSubgroup rawData K true (pairedNode j)⊔
      canonicalRootSubgroup rawData K true (pairedPartner j) := by
  rw [orbitNegativeGroup,orbitPositiveGroup_paired,Subgroup.map_sup,
    simple_group_opposition,simple_group_opposition]

theorem orbitNegativeGroup_singleton (K : Type) [Field K] (j : Fin 2) :
    orbitNegativeGroup K (singletonOrbit j)=canonicalRootSubgroup rawData K true (node j) := by
  rw [orbitNegativeGroup,orbitPositiveGroup_singleton,simple_group_opposition]

theorem negative_inf_orbitFlag (K : Type) [Field K] (a : Fin 4) :
    Negative K⊓orbitFlag K a=orbitNegativeGroup K a := by
  have h := negative_inf_reverse_flag_eq_opposition_zero A CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K
      (orbitHeight a) (fun k=>orbitHeight_nonneg a k.val.val k.property)
  rw [zeroFunctionalGroup_eq_orbitPositiveGroup] at h
  simpa only [orbitFlag,orbitNegativeGroup,rawOpposition,
    CFSGNormTwoGeckQuadraticMembership.height_latticeWeight] using h

def fixedOrbitNegative (K : Type) [Field K] (sigma : K≃+*K) (a : Fin 4) :
    Subgroup (signedFixed K sigma true) :=
  (orbitNegativeGroup K a).subgroupOf (signedFixed K sigma true)

theorem fixedOrbitNegative_paired (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (j : Fin 2) :
    fixedOrbitNegative K sigma (pairedOrbit j)=(pairedFixedHom K sigma hsigma true j).range := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    have hj : g.val∈canonicalRootSubgroup rawData K true (pairedNode j)⊔
        canonicalRootSubgroup rawData K true (pairedPartner j) := by
      change g.val∈orbitNegativeGroup K (pairedOrbit j) at hg
      rwa [orbitNegativeGroup_paired] at hg
    obtain ⟨a,ha⟩ := exists_paired_parameter_of_fixed K sigma hsigma true j g.val hj g.property.2
    exact ⟨Multiplicative.ofAdd a,Subtype.ext ha.symm⟩
  · rintro ⟨a,rfl⟩
    change rawPairedHom K sigma true j a∈orbitNegativeGroup K (pairedOrbit j)
    rw [orbitNegativeGroup_paired,←rawPairHom_range]
    exact ⟨(a,Multiplicative.ofAdd (sigma a.toAdd)),rfl⟩

theorem fixedOrbitNegative_singleton (K : Type) [Field K] (sigma : K≃+*K) (j : Fin 2) :
    fixedOrbitNegative K sigma (singletonOrbit j)=(singletonFixedHom K sigma true j).range := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    have hj : g.val∈canonicalRootSubgroup rawData K true (node j) := by
      change g.val∈orbitNegativeGroup K (singletonOrbit j) at hg
      rwa [orbitNegativeGroup_singleton] at hg
    obtain ⟨a,ha⟩ := hj
    have hfix : CFSGTwistedE6GeckMatrixTwist.unitTwist K sigma
        (canonicalRoot rawData K true (node j) a)=canonicalRoot rawData K true (node j) a := by
      rw [ha]
      exact g.property.2
    have haFix := (singleton_fixed_iff K sigma true j a).mp hfix
    let af : fixedCoefficient K sigma := ⟨a,haFix⟩
    exact ⟨Multiplicative.ofAdd af,Subtype.ext ha⟩
  · rintro ⟨a,rfl⟩
    change rawSingletonHom K true j (Multiplicative.ofAdd (a.toAdd : K))∈
      orbitNegativeGroup K (singletonOrbit j)
    rw [orbitNegativeGroup_singleton]
    exact ⟨(a.toAdd : K),rfl⟩

end SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeOrbitRootGroups
