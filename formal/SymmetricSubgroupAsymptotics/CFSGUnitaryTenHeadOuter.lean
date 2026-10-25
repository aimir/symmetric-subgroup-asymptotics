import SymmetricSubgroupAsymptotics.UnitaryTenHeadScaledFrameNumerics
import SymmetricSubgroupAsymptotics.CFSGUnitaryProperIndexOuterUpper
import SymmetricSubgroupAsymptotics.CFSGUnitaryCoprimeOuterCardinality

/-! Outer bounds on the same ten original unitary models. The binary
rank-three case uses the coprime projective kernel; every other case
uses the proved semilinear reconstruction and the actual field exponent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadOuter
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates
open UnitaryTenHeadScaledFrameNumerics

theorem outer_card_le (j : Fin 10) (r : ℕ) (q : CFSG.PrimePower)
    (hpar : parameters j=(r,q.order))
    [IsSimpleGroup (CFSG.Models.TwistedA r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedA r q)) :
    Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ outerCeiling j := by
  have hrank : r=(parameters j).1 := (congrArg Prod.fst hpar).symm
  have horder : q.order=(parameters j).2 := (congrArg Prod.snd hpar).symm
  by_cases hb : parameters j=(3,2)
  · have hr : r=3 := hrank.trans (congrArg Prod.fst hb)
    have hq : q.order=2 := horder.trans (congrArg Prod.snd hb)
    rcases hr with rfl
    simpa only [outerCeiling,if_pos hb] using
      CFSGUnitaryCoprimeOuterCardinality.binary_rank_three_or_four_outer_card_le_two
        q hq 0 (Or.inl rfl) hn
  · have hp := parameter_admissible j
    have hr : 2 ≤ r := by omega
    have hsmall : r=2 → q.order≠2 := by omega
    have hf : q.exponent ≤ Nat.log 2 q.order :=
      Nat.le_log_of_pow_le (by decide)
        (show 2^q.exponent ≤ q.order from
          Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
    have ho := twistedA_admissible_raw_outer_order_le r hr q hsmall hn
    calc
      _ ≤ 2*(r+1)*q.exponent := ho
      _ ≤ 2*(r+1)*Nat.log 2 q.order := Nat.mul_le_mul_left _ hf
      _ = outerCeiling j := by
        simp only [outerCeiling,if_neg hb,hrank,horder]

end SymmetricSubgroupAsymptotics.CFSGUnitaryTenHeadOuter
