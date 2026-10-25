import SymmetricSubgroupAsymptotics.CFSGPSLTwoTwentyFiveIndex
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneOddClassCube
import SymmetricSubgroupAsymptotics.CFSGPSLTwoOuterBound

/-! The field-order25 packet uses the original odd trace class bound,
original outer bound and actual15-point proper-index obstruction. The
scaled inequality is derived, rather than added as a profile premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoTwentyFiveScaledClassPacket
open PrimitiveSocleRawStructure

private theorem parameters (q : CFSG.PrimePower) (hq : q.order=25) :
    q.prime=5 ∧ q.exponent=2 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 5)
    q.exponent_pos.ne' (by decide : (2:ℕ)≠0)
    (show q.prime^q.exponent=5^2 from hq)

theorem class_card_le_fifteen (q : CFSG.PrimePower) (hq : q.order=25) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q))≤15 := by
  have hp := (parameters q hq).1
  have hh := CFSGTypeARankOneOddClassCube.twice_class_card_le q (by omega)
  omega

theorem outer_card_le_four (q : CFSG.PrimePower) (hq : q.order=25) :
    Nat.card (Outer (CFSG.Models.A 1 q))≤4 := by
  have he := (parameters q hq).2
  simpa only [he,Nat.reduceMul] using CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hq : q.order=25)
    (K : Subgroup (CFSG.Models.A 1 q)) (hK : K≠⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.A 1 q))*
      Nat.card (Outer (CFSG.Models.A 1 q)))^3≤3^K.index := by
  have hB : Nat.card (ConjClasses (CFSG.Models.A 1 q))*
      Nat.card (Outer (CFSG.Models.A 1 q))≤15*4 :=
    Nat.mul_le_mul (class_card_le_fifteen q hq) (outer_card_le_four q hq)
  have hscalar : 25*((15:ℕ)*4)^3≤3^15 := by norm_num
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hB 3)).trans hscalar).trans
    (Nat.pow_le_pow_right (by decide)
      (CFSGPSLTwoTwentyFiveIndex.proper_index_ge_fifteen q hq K hK))

end SymmetricSubgroupAsymptotics.CFSGPSLTwoTwentyFiveScaledClassPacket
