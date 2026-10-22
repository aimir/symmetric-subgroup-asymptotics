import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceBudget
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTracePilot

/-! Actual complement trace bounds from the two selected full-linear-order
receipts. In particular the degree81 bound applies to EVERY complement,
including soluble/commutative ones, and does not assert a cube-order bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem complementTrace_abelianLength_le_eight_of_degree49
    (P : PrimitiveAffineProfile G X) (hp : MulAction.IsPreprimitive G X)
    (x : X) (he : Nat.card X=49) (T : FixedTargetCompositionTrace (P.complement x)) :
    T.envelope.abelianLength ≤ 8 := by
  have h := P.complementTrace_abelianLength_le_fullLinearOmega hp x
    (p := 7) (d := 2) (by decide) (by decide) (by norm_num [he]) T
  simpa only [CFSGPrimitiveAffineOrderTracePilot.selected_GL_two_seven] using h

theorem complementTrace_abelianLength_le_seventeen_of_degree81
    (P : PrimitiveAffineProfile G X) (hp : MulAction.IsPreprimitive G X)
    (x : X) (he : Nat.card X=81) (T : FixedTargetCompositionTrace (P.complement x)) :
    T.envelope.abelianLength ≤ 17 := by
  have h := P.complementTrace_abelianLength_le_fullLinearOmega hp x
    (p := 3) (d := 4) (by decide) (by decide) (by norm_num [he]) T
  simpa only [CFSGPrimitiveAffineOrderTracePilot.selected_GL_four_three] using h

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
