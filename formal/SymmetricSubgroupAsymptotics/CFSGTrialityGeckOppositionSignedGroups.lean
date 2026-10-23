import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckNegativeOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLineNormalizers
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear

/-! The literal relative opposition exchanges both signs of the whole
root groups and each orbit-zero group. This uses its proved lattice
minus-one action and actual root-line transport, retaining its diagonal
square rather than asserting that the Weyl word is an involution. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOppositionSignedGroups
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckRelativeOpposition CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckOrbitZeroFunctionalGroup CFSGTrialityGeckNegativeOrbitRootGroups
open CFSGTrialityGeckFixedOrbitRootGroups CFSGTrialityGeckMatrixTwist
open CFSGNormTwoCoordinateNegativeSimpleRootLine CFSGNormTwoCoordinateCanonicalSimpleRootLine
open CFSGNormTwoCoordinateRootWeylAction CFSGNormTwoCoordinateRootLineNormalizers
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckColumns CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckPositivePGroup CFSGTrialityGeckSectionHeightMembership
open CFSGFixedSubgroupConjugation CFSGCentralTwistedCommutatorLift
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem simple_opposition_label (i : Fin 4) :
    wordRoot A hs hp Base Index oppositionWord (Index i)=negativeIndex A hs hp (Index i) := by
  apply Subtype.ext
  rw [negative_val]
  exact (wordLinear_root A hs hp Base Index oppositionWord (Index i)).symm.trans
    (opposition_linear_neg _)

private theorem negative_simple_opposition_label (i : Fin 4) :
    wordRoot A hs hp Base Index oppositionWord (negativeIndex A hs hp (Index i))=Index i := by
  apply Subtype.ext
  calc
    _=-(negativeIndex A hs hp (Index i)).val :=
      (wordLinear_root A hs hp Base Index oppositionWord _).symm.trans (opposition_linear_neg _)
    _=(Index i : CFSGNormTwoRootPairing.Roots A).val := by rw [negative_val,neg_neg]

theorem opposition_simple_group_map (K : Type) [Field K] (neg : Bool) (i : Fin 4) :
    (canonicalRootSubgroup rawData K neg i).map (MulAut.conj (relativeOpposition K)).toMonoidHom=
      canonicalRootSubgroup rawData K (!neg) i := by
  have hpos := rootSubgroup_simple_eq_canonical A hd hs hp ho K i
  have hneg := rootSubgroup_negative_simple_eq_canonical A hd hs hp ho K i
  change RootLine K (Index i)=canonicalRootSubgroup rawData K false i at hpos
  change RootLine K (negativeIndex A hs hp (Index i))=canonicalRootSubgroup rawData K true i at hneg
  cases neg
  · have hh := rootSubgroup_map_word A hd hs hp ho K oppositionWord (Index i)
    change (RootLine K (Index i)).map
      (MulAut.conj (canonicalWord rawData K oppositionWord)).toMonoidHom=
      RootLine K (wordRoot A hs hp Base Index oppositionWord (Index i)) at hh
    rw [simple_opposition_label,hpos,hneg] at hh
    simpa only [relativeOpposition,word_eq_canonicalWord] using hh
  · have hh := rootSubgroup_map_word A hd hs hp ho K oppositionWord (negativeIndex A hs hp (Index i))
    change (RootLine K (negativeIndex A hs hp (Index i))).map
      (MulAut.conj (canonicalWord rawData K oppositionWord)).toMonoidHom=
      RootLine K (wordRoot A hs hp Base Index oppositionWord (negativeIndex A hs hp (Index i))) at hh
    rw [negative_simple_opposition_label,hneg,hpos] at hh
    simpa only [relativeOpposition,word_eq_canonicalWord] using hh

theorem opposition_signed_group_map (K : Type) [Field K] (neg : Bool) :
    (rootGroup A hs hp Base Index K neg).map (MulAut.conj (relativeOpposition K)).toMonoidHom=
      rootGroup A hs hp Base Index K (!neg) := by
  have he (e:Bool) : rootGroup A hs hp Base Index K e=
      ⨆i:Fin 4,canonicalRootSubgroup rawData K e i :=
    rootGroup_eq_iSup_canonical A hd hs hp ho K e
  rw [he,Subgroup.map_iSup]
  simp only [opposition_simple_group_map]
  exact (he (!neg)).symm

theorem opposition_signedFixed_map (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool) :
    (signedFixed K sigma neg).map (MulAut.conj (relativeOpposition K)).toMonoidHom=
      signedFixed K sigma (!neg) := by
  rw [signedFixed,map_inf_fixed _ _ _ (relativeOpposition_fixed K sigma),opposition_signed_group_map]
  rfl

theorem opposition_orbit_positive_map (K : Type) [Field K] (a : Bool) :
    (orbitRootGroup K a).map (MulAut.conj (relativeOpposition K)).toMonoidHom=
      orbitNegativeGroup K a := by
  cases a
  · change (CFSGTrialityGeckShortComplementFactor.outerGroup K).map _=_
    rw [outerGroup_eq_iSup,Subgroup.map_iSup]
    simp only [opposition_simple_group_map]
    rfl
  · exact opposition_simple_group_map K false 1

theorem opposition_orbit_negative_map (K : Type) [Field K] (a : Bool) :
    (orbitNegativeGroup K a).map (MulAut.conj (relativeOpposition K)).toMonoidHom=
      orbitRootGroup K a := by
  cases a
  · change (⨆i:Fin 3,canonicalRootSubgroup rawData K true
      (CFSGTrialityFixedWeylWords.outerNode i)).map _=_
    rw [Subgroup.map_iSup]
    simp only [opposition_simple_group_map]
    exact (outerGroup_eq_iSup K).symm
  · exact opposition_simple_group_map K true 1

theorem opposition_fixedOrbit_positive_map (q : CFSG.PrimePower) (a : Bool) :
    (fixedOrbitRootGroup q a).map (MulAut.conj (relativeOpposition (q.Extension 3))).toMonoidHom=
      fixedOrbitNegative q a := by
  rw [fixedOrbitRootGroup,map_inf_fixed _ _ _ (relativeOpposition_fixed _ _),opposition_orbit_positive_map]
  rfl

theorem opposition_fixedOrbit_negative_map (q : CFSG.PrimePower) (a : Bool) :
    (fixedOrbitNegative q a).map (MulAut.conj (relativeOpposition (q.Extension 3))).toMonoidHom=
      fixedOrbitRootGroup q a := by
  rw [fixedOrbitNegative,map_inf_fixed _ _ _ (relativeOpposition_fixed _ _),opposition_orbit_negative_map]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOppositionSignedGroups
