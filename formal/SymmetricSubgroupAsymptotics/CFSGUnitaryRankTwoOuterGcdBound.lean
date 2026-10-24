import SymmetricSubgroupAsymptotics.CFSGTwistedA2OuterOrder
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoLayerOrbitCardinality

/-! The actual projective rank-two torus kernel lies in its first-weight
kernel. Its gcd(3,q+1) cardinal bound refines the original outer count;
no projective centre formula or abstract automorphism classification is
assumed. The only simplicity premise is for the same original model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists
open CFSGTwistedA2DiagonalTorus PrimitiveSocleRawStructure CFSGOuterCardinalityAlignment

theorem rankTwoProjectiveTorus_kernel_le_firstWeight
    (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (rankTwoProjectiveTorus q hq).ker ≤ (rankTwoFirstWeightHom q).ker := by
  intro z hz
  let b := CFSGTwistedA2UnipotentParameters.particular q hq 1
  have hb := CFSGTwistedA2UnipotentParameters.particular_spec q hq 1
  let u : naturalUnipotent 2 q :=
    ⟨CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
      (definingFieldAutomorphism q 2) 1 b,
      rankTwoOldUpper_le q ⟨1,b,hb,rfl⟩⟩
  have hc : rankTwoDerivedCover q hq (rankTwoNaturalTorus q z) ∈
      Subgroup.center (commutator (Fixed 2 q)) := (QuotientGroup.eq_one_iff _).mp hz
  have he := rankTwo_central_cover_conjugates_upper q hq (rankTwoNaturalTorus q z) hc u
  change torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) z *
      CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
        (definingFieldAutomorphism q 2) 1 b *
      (torusNatural (q.Extension 2) (definingFieldAutomorphism q 2) z)⁻¹ = _ at he
  rw [torus_conjugate_upper _ _ (fun x => extension_two_pow_twice q x) z (Units.ne_zero z)] at he
  have hw := congrArg (fun x : NaturalElementary (q.Extension 2) 2 =>
    (x.val : Mat (q.Extension 2) 2) 0 1) he
  change (CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
      (definingFieldAutomorphism q 2)
      (firstWeight (q.Extension 2) (definingFieldAutomorphism q 2) z * 1)
      (centralWeight (q.Extension 2) (definingFieldAutomorphism q 2) z * b)).val.val 0 1 =
    (CFSGTwistedA2UnipotentArrays.upperNatural (q.Extension 2)
      (definingFieldAutomorphism q 2) 1 b).val.val 0 1 at hw
  rw [CFSGTwistedA2UnipotentArrays.upperNatural_val,
    CFSGTwistedA2UnipotentArrays.upperNatural_val] at hw
  change rankTwoFirstWeightHom q z = 1
  apply Units.ext
  simpa [rankTwoFirstWeightHom_val,firstWeight,
    CFSGTwistedA2UnipotentArrays.upperArray] using hw

theorem rankTwoProjectiveTorus_kernel_card_le_gcd
    (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    Nat.card (rankTwoProjectiveTorus q hq).ker ≤ (q.order+1).gcd 3 :=
  (Nat.card_le_card_of_injective
    (Subgroup.inclusion (rankTwoProjectiveTorus_kernel_le_firstWeight q hq))
    (Subgroup.inclusion_injective _)).trans (rankTwoFirstWeight_kernel_card_le q)

theorem rankTwoProjectiveTorus_card_lower_gcd
    (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    q.order^2-1 ≤ (q.order+1).gcd 3 * Nat.card (rankTwoProjectiveTorus q hq).range := by
  have he : Nat.card (q.Extension 2)ˣ =
      Nat.card (rankTwoProjectiveTorus q hq).ker *
        Nat.card (rankTwoProjectiveTorus q hq).range := by
    rw [← (rankTwoProjectiveTorus q hq).ker.card_mul_index,Subgroup.index_ker]
  have hc := Nat.mul_le_mul_right (Nat.card (rankTwoProjectiveTorus q hq).range)
    (rankTwoProjectiveTorus_kernel_card_le_gcd q hq)
  rw [← he,Nat.card_units,extension_two_card] at hc
  exact hc

theorem twistedA_rankTwo_outer_order_le_gcd_exponent
    (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    [IsSimpleGroup (CFSG.Models.TwistedA 2 q)] :
    Nat.card (Outer (CFSG.Models.TwistedA 2 q)) ≤ 2*((q.order+1).gcd 3)*q.exponent := by
  letI : Finite (CFSG.Models.TwistedA 2 q) :=
    Finite.of_surjective (rankTwoProjectiveCover q hq) (rankTwoProjectiveCover_surjective q hq)
  apply outer_card_le_of_aligned_bound (rankTwoPairStabilizer q hq)
    (rankTwoProjectiveTorus q hq).range
    (rankTwo_inner_align_pair q hq) (rankTwo_inner_torus_mem_pair q hq)
    (rankTwo_inner_torus_injective q hq) (d := 2*((q.order+1).gcd 3)*q.exponent)
  calc
    Nat.card (rankTwoPairStabilizer q hq) ≤ (q.order^2-1)*(2*q.exponent) :=
      rankTwo_pairStabilizer_card_le q hq
    _ ≤ ((q.order+1).gcd 3*Nat.card (rankTwoProjectiveTorus q hq).range)*(2*q.exponent) :=
      Nat.mul_le_mul_right _ (rankTwoProjectiveTorus_card_lower_gcd q hq)
    _ = Nat.card (rankTwoProjectiveTorus q hq).range *
        (2*((q.order+1).gcd 3)*q.exponent) := by ring

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
