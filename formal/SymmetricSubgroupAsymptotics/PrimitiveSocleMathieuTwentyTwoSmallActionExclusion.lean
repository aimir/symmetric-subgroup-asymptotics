import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedWordOrder
import SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion

/-! The checked selected prime-period word in the literal pinned M22
model excludes that SAME actual simple socle factor on at most ten
points. The original action and model equivalence are retained. Only
11-divisibility and the actual factorial embedding are used; no order
formula, action catalogue, or elementary-Sylow hypothesis is present. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleMathieuTwentyTwoSmallActionExclusion
open PrimitiveSocleRawStructure

/-- This excludes M22 for every actual faithful source of degree at most
ten, including the original retained global failed-half witness. -/
theorem not_mathieu_twenty_two
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (hdegree : Nat.card X ≤ 10)
    (e : D.Simple ≃* CFSG.Models.Mathieu22) : False := by
  have hd := PrimitiveSocleElevenPointTitsExclusion.simple_card_dvd_degree_factorial D
  rw [Nat.card_congr e.toEquiv] at hd
  have h11 : 11 ∣ (Nat.card X).factorial :=
    CFSGMathieuTwentyTwoSelectedWordOrder.eleven_dvd_order.trans hd
  have hle : 11 ≤ Nat.card X := (by decide : Nat.Prime 11).dvd_factorial.mp h11
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleMathieuTwentyTwoSmallActionExclusion
