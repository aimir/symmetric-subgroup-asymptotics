import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSimpleChartWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeFunctionalIntersection
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation

/-! The reverse integral flag recognizes the full negative orbit-zero
subgroup. A genuinely fixed simple Weyl word identifies its fixed part
with the positive parameter chart, so fixedness is transported on actual
matrices and never inferred from a fixed quotient class. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckNegativeOrbitRootGroups
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityFixedWeylWords
open CFSGTrialityGeckOrbitZeroFunctionalGroup CFSGTrialityGeckFixedOrbitRootGroups
open CFSGTrialityGeckShortComplementFactor CFSGTrialityGeckSimpleChartWeyl
open CFSGTrialityGeckSimpleOrbitFlags CFSGTrialityD4SimpleOrbitSupport
open CFSGNormTwoCoordinateNegativeFunctionalIntersection CFSGNormTwoGeckFieldOpposition
open CFSGTrialityGeckMatrixTwist
open CFSGNormTwoGeckHeightSupport CFSGTrialityGeckFixedRootWords
open CFSGCentralTwistedCommutatorLift CFSGFixedSubgroupConjugation
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem outerGroup_eq_iSup (K : Type) [Field K] :
    outerGroup K=⨆i:Fin 3,canonicalRootSubgroup rawData K false (outerNode i) := by
  rw [outerGroup,outerProductHom,MonoidHom.noncommPiCoprod_range]
  congr 1

def orbitNegativeGroup (K : Type) [Field K] (a : Bool) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  if a then canonicalRootSubgroup rawData K true 1 else
    ⨆i:Fin 3,canonicalRootSubgroup rawData K true (outerNode i)

private theorem root_group_map {G : Type*} [Group G] (K : Type) [Field K]
    (e : MulAut G) (x y : K→G) (X Y : Subgroup G)
    (hX : (X:Set G)=Set.range x) (hY : (Y:Set G)=Set.range y)
    (he : ∀t,e (x t)=y (-t)) : X.map e.toMonoidHom=Y := by
  ext g
  constructor
  · rintro ⟨u,hu,rfl⟩
    change u∈(X:Set G) at hu
    rw [hX] at hu
    obtain ⟨t,rfl⟩ := hu
    change e (x t)∈(Y:Set G)
    rw [hY]
    exact ⟨-t,(he t).symm⟩
  · intro hg
    change g∈(Y:Set G) at hg
    rw [hY] at hg
    obtain ⟨t,rfl⟩ := hg
    refine ⟨x (-t),?_,?_⟩
    · change x (-t)∈(X:Set G)
      rw [hX]
      exact ⟨-t,rfl⟩
    · simpa only [neg_neg] using he (-t)

theorem orbit_word_map_positive (K : Type) [Field K] (a : Bool) :
    (orbitRootGroup K a).map (MulAut.conj (canonicalWord rawData K (orbitWord a))).toMonoidHom=
      orbitNegativeGroup K a := by
  cases a
  · change (outerGroup K).map (MulAut.conj (CFSGTrialityGeckFixedRootWords.shortWeyl K)).toMonoidHom=_
    rw [outerGroup_eq_iSup,Subgroup.map_iSup]
    change (⨆i:Fin 3,(canonicalRootSubgroup rawData K false (outerNode i)).map
      (MulAut.conj (CFSGTrialityGeckFixedRootWords.shortWeyl K)).toMonoidHom)=_
    congr 1
    funext i
    exact root_group_map K (MulAut.conj (CFSGTrialityGeckFixedRootWords.shortWeyl K)) _ _ _ _ rfl rfl
      (outer_word_conjugates_root K i)
  · exact root_group_map K (MulAut.conj (canonicalWord rawData K (orbitWord true)))
      _ _ _ _ rfl rfl (middle_word_conjugates K)

theorem orbit_opposition_map (K : Type) [Field K] (a : Bool) :
    (orbitRootGroup K a).map
      (MulAut.conj (oppositionUnit A hs hp Base K)).toMonoidHom=orbitNegativeGroup K a := by
  have hm (i:Fin 4) : (canonicalRootSubgroup rawData K false i).map
      (MulAut.conj (oppositionUnit A hs hp Base K)).toMonoidHom=
        canonicalRootSubgroup rawData K true i := by
    ext g
    constructor
    · rintro ⟨u,⟨t,rfl⟩,rfl⟩
      exact ⟨t,(canonicalRoot_conjugate A hs hp Base Index K false i t).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨canonicalRoot rawData K false i t,⟨t,rfl⟩,
        canonicalRoot_conjugate A hs hp Base Index K false i t⟩
  cases a
  · change (outerGroup K).map _=_
    rw [outerGroup_eq_iSup,Subgroup.map_iSup]
    simp only [hm]
    rfl
  · exact hm 1

theorem negative_inf_orbitFlag (K : Type) [Field K] (a : Bool) :
    CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp Base Index K true⊓orbitFlag K a=
      orbitNegativeGroup K a := by
  have hh := negative_inf_reverse_flag_eq_opposition_zero A hd hs hp ho K
    (orbitHeight a) (fun k=>orbitHeight_nonnegative a k.val.val k.property)
  rw [zeroFunctionalGroup_eq_orbitRootGroup] at hh
  change (CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp Base Index K true⊓
    CFSGGradedMatrixTriangularUnits.triangularUnits (fun j=>
      -orbitHeight a (CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp Base j)))=
      (orbitRootGroup K a).map (MulAut.conj (oppositionUnit A hs hp Base K)).toMonoidHom at hh
  rw [orbit_opposition_map] at hh
  simpa only [orbitFlag,CFSGNormTwoGeckQuadraticMembership.height_latticeWeight] using hh

def fixedOrbitNegative (q : CFSG.PrimePower) (a : Bool) :
    Subgroup (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ :=
  orbitNegativeGroup (q.Extension 3) a⊓
    fixedSubgroup (unitTwist (q.Extension 3) (definingFieldAutomorphism q 3))

theorem fixedOrbitRootGroup_map (q : CFSG.PrimePower) (a : Bool) :
    (fixedOrbitRootGroup q a).map
      (MulAut.conj (canonicalWord rawData (q.Extension 3) (orbitWord a))).toMonoidHom=
        fixedOrbitNegative q a := by
  have hW : unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (canonicalWord rawData (q.Extension 3) (orbitWord a))=
        canonicalWord rawData (q.Extension 3) (orbitWord a) := by
    cases a
    · exact shortWeyl_fixed _ _
    · exact longWeyl_fixed _ _
  rw [fixedOrbitRootGroup,map_inf_fixed _ _ _ hW,orbit_word_map_positive]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckNegativeOrbitRootGroups
