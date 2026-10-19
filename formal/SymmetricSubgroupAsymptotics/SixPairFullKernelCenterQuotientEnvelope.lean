import SymmetricSubgroupAsymptotics.SixPairFullKernelQuotientCoordinates
import SymmetricSubgroupAsymptotics.TwoBinaryThreeCubicTopTypes
import SymmetricSubgroupAsymptotics.ThreePointTransitiveCubicMembership
import SymmetricSubgroupAsymptotics.ScalarFourCentralTopEquiv
import SymmetricSubgroupAsymptotics.ScalarFourCentralRankTwoTightEnvelope

/-! Both actual transitive three-label tops enter the same tightened
complete original-quotient envelope for the actual center quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelCenterQuotientEnvelope
open SixPairFullKernelCenter Non2UnipotentPrefixFiniteMenu

variable {X I : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

theorem complete_sum_le [MulAction.IsPretransitive U X]
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      completeQuotientWeight (R := U ⧸ centerImage F E) J)≤
      (2 : ℝ)^(256 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(81 : ℕ)) 15 b := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let T := C.top.range
  have ht := C.top_range_transitive (fun x y => MulAction.exists_smul_eq U x y)
  letI : MulAction.IsPretransitive T (Fin 3) := ⟨ht⟩
  have hr := ThreePointTransitiveCubicMembership.frame_rotation_mem C
    (fun x y => MulAction.exists_smul_eq U x y)
  let D := SixPairFullKernelQuotientCoordinates.coordinates F E hfull hr
  rcases SixPairThreePointNormalTop.cardinal_cases T with h3 | h6
  · let e := TwoBinaryThreePermutationCoordinates.cubicEquivOfCardThree T hr h3
    let A := D.topEquiv e.symm
    have ha : A.cubic=Multiplicative.ofAdd (1 : ZMod 3) := by
      change e.symm (e (Multiplicative.ofAdd 1))=Multiplicative.ofAdd 1
      exact e.symm_apply_apply _
    have hh := A.complete_quotient_envelope_two_tight (by decide) (by decide) ha
      OddMarkerTernaryChart.embedding OddMarkerTernaryChart.embedding_injective hZmud lit b
    apply hh.trans
    apply add_le_add le_rfl
    unfold BinaryKernelRankTailNumerics.raw
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_right₀ _ (by decide : 12≤15)
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)
  · let e := TwoBinaryThreePermutationCoordinates.symmetricEquivOfCardSix T h6
    have ho : orderOf D.cubic=3 := TwoBinaryThreePermutationCoordinates.cubic_order T hr
    exact D.symmetric_complete_quotient_envelope_two_tight e (by decide) (by decide) ho
      hZmud lit b

end SymmetricSubgroupAsymptotics.SixPairFullKernelCenterQuotientEnvelope
