import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNegativeOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedParabolics

/-! The genuine fixed negative group meets each actual positive minimal
parabolic in precisely the corresponding negative relative root group.
The reverse inclusion uses the literal fixed Weyl chart, not a lifting
assertion for a fixed quotient or a supplied parabolic recognition. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckNegativeParabolicRootIntersection
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityGeckNegativeOrbitRootGroups
open CFSGTrialityGeckOrbitZeroFunctionalGroup CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckMinimalOvergroups CFSGTrialityGeckFixedUpperNormalizer
open CFSGTrialityGeckGeneratedParabolics CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckRootGeneratedPGroup
open CFSGNormTwoCoordinateZeroFunctionalSupport CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem orbitRootGroup_le_positive (K : Type) [Field K] (a : Bool) :
    orbitRootGroup K a≤Positive K := by
  have hh := zeroFunctionalGroup_le_positive A hd hs hp ho K (orbitHeight a)
  rwa [zeroFunctionalGroup_eq_orbitRootGroup] at hh

private theorem fixed_positive_le_upperIn (K : Type) [Field K] (sigma : K≃+*K) :
    signedFixed K sigma false≤upperIn K (fixedRootGenerated K sigma) :=
  le_inf (inf_le_left.trans (positive_le_envelope K)) (signedFixed_le_generated K sigma false)

theorem fixed_negative_inf_simpleParabolic (q : CFSG.PrimePower) (a : Bool) :
    signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true⊓
      simpleParabolic (q.Extension 3)
        (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) a=
          fixedOrbitNegative q a := by
  apply le_antisymm
  · intro g hg
    have haxis : g∈orbitNegativeGroup (q.Extension 3) a := by
      rw [←negative_inf_orbitFlag]
      exact ⟨hg.1.1,simpleParabolic_le_orbitFlag (q.Extension 3)
        (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) a hg.2⟩
    exact ⟨haxis,hg.1.2⟩
  · intro g hg
    have hV : g∈signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true := by
      have hle : orbitNegativeGroup (q.Extension 3) a≤
          CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp Base Index (q.Extension 3) true :=
        (negative_inf_orbitFlag (q.Extension 3) a).ge.trans inf_le_left
      exact ⟨hle hg.1,hg.2⟩
    refine ⟨hV,?_⟩
    rw [←fixedOrbitRootGroup_map q a] at hg
    obtain ⟨v,hv,rfl⟩ := hg
    let P := simpleParabolic (q.Extension 3)
      (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) a
    let W := canonicalWord CFSGTrialityGeckDiagramCovariance.rawData (q.Extension 3) (orbitWord a)
    have hW : W∈P := (show Subgroup.closure {W}≤P from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))
    have hvU : v∈signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) false :=
      ⟨orbitRootGroup_le_positive (q.Extension 3) a hv.1,hv.2⟩
    have hvP : v∈P :=
      (show upperIn (q.Extension 3)
          (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))≤P from le_sup_left)
        (fixed_positive_le_upperIn _ _ hvU)
    change W*v*W⁻¹∈P
    exact P.mul_mem (P.mul_mem hW hvP) (P.inv_mem hW)

def negativeOrbitRootGenerated (q : CFSG.PrimePower) (a : Bool) :
    Subgroup (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) :=
  (fixedOrbitNegative q a).subgroupOf
    (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3))

theorem negative_rootPart_inf_parabolicGenerated (q : CFSG.PrimePower) (a : Bool) :
    rootPart (q.Extension 3) (definingFieldAutomorphism q 3) true⊓
      parabolicGenerated (q.Extension 3) (definingFieldAutomorphism q 3) a=
        negativeOrbitRootGenerated q a := by
  ext x
  constructor
  · intro hx
    have hm : x.val∈signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true⊓
        simpleParabolic (q.Extension 3)
          (fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) a :=
      ⟨hx.1,hx.2⟩
    rw [fixed_negative_inf_simpleParabolic] at hm
    exact hm
  · intro hx
    have hm : x.val∈fixedOrbitNegative q a := hx
    rw [←fixed_negative_inf_simpleParabolic] at hm
    exact ⟨hm.1,hm.2⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckNegativeParabolicRootIntersection
