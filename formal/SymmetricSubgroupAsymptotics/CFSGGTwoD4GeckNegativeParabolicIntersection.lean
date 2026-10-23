import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOrbitRootGroups
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedParabolics

/-! The actual identity-twist negative root part meets each positive
minimal parabolic in exactly its negative simple orbit chart. Fixed
Weyl conjugation proves the reverse inclusion on literal matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckNegativeParabolicIntersection
open CFSGGTwoD4GeckOrbitRootGroups CFSGTrialityGeckNegativeOrbitRootGroups
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckOrbitZeroFunctionalGroup CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityGeckMinimalOvergroups CFSGTrialityGeckFixedUpperNormalizer
open CFSGTrialityGeckGeneratedParabolics CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckNormalizerEnvelope CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckRootGeneratedPGroup CFSGNormTwoCoordinateZeroFunctionalSupport
open CFSGSerreQuadraticWeylWord
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

private theorem orbitRootGroup_le_positive (a : Bool) : orbitRootGroup K a ≤ Positive K := by
  have hh := zeroFunctionalGroup_le_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K (orbitHeight a)
  rwa [zeroFunctionalGroup_eq_orbitRootGroup] at hh

theorem fixed_negative_inf_simpleParabolic (a : Bool) :
    signedFixed K (RingEquiv.refl K) true ⊓ simpleParabolic K J a = fixedOrbitNegative K a := by
  apply le_antisymm
  · intro g hg
    have haxis : g ∈ orbitNegativeGroup K a := by
      rw [←negative_inf_orbitFlag]
      exact ⟨hg.1.1, simpleParabolic_le_orbitFlag K J a hg.2⟩
    exact ⟨haxis, hg.1.2⟩
  · intro g hg
    have hV : g ∈ signedFixed K (RingEquiv.refl K) true := by
      have hle : orbitNegativeGroup K a ≤ Negative K :=
        (negative_inf_orbitFlag K a).ge.trans inf_le_left
      exact ⟨hle hg.1, hg.2⟩
    refine ⟨hV, ?_⟩
    rw [←fixedOrbitPositive_map K a] at hg
    obtain ⟨v, hv, rfl⟩ := hg
    let P := simpleParabolic K J a
    let W := canonicalWord rawData K (orbitWord a)
    have hW : W ∈ P := (show Subgroup.closure {W} ≤ P from le_sup_right)
      (Subgroup.subset_closure (Set.mem_singleton _))
    have hvU : v ∈ signedFixed K (RingEquiv.refl K) false :=
      ⟨orbitRootGroup_le_positive K a hv.1, hv.2⟩
    have hvB : v ∈ upperIn K J :=
      ⟨positive_le_envelope K hvU.1, signedFixed_le_generated K (RingEquiv.refl K) false hvU⟩
    have hvP : v ∈ P := (show upperIn K J ≤ P from le_sup_left) hvB
    change W * v * W⁻¹ ∈ P
    exact P.mul_mem (P.mul_mem hW hvP) (P.inv_mem hW)

def negativeOrbitRootGenerated (a : Bool) : Subgroup J := (fixedOrbitNegative K a).subgroupOf J

def positiveOrbitRootGenerated (a : Bool) : Subgroup J := (fixedOrbitPositive K a).subgroupOf J

theorem negative_rootPart_inf_parabolicGenerated (a : Bool) :
    rootPart K (RingEquiv.refl K) true ⊓ parabolicGenerated K (RingEquiv.refl K) a =
      negativeOrbitRootGenerated K a := by
  ext x
  constructor
  · intro hx
    have hm : x.val ∈ signedFixed K (RingEquiv.refl K) true ⊓ simpleParabolic K J a :=
      ⟨hx.1, hx.2⟩
    rw [fixed_negative_inf_simpleParabolic] at hm
    exact hm
  · intro hx
    have hm : x.val ∈ fixedOrbitNegative K a := hx
    rw [←fixed_negative_inf_simpleParabolic] at hm
    exact ⟨hm.1, hm.2⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckNegativeParabolicIntersection
