import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceBudget

/-! Two additional selected binary full-linear-order prime-factor budgets,
after the earlier selected order-charge pilot. Actual traces are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceBinary

theorem selected_binary_receipts :
    ArithmeticFunction.cardFactors (fullLinearOrder 2 7)=30 ∧
    ArithmeticFunction.cardFactors (fullLinearOrder 2 8)=40 := by
  unfold fullLinearOrder
  decide +kernel

end CFSGPrimitiveAffineOrderTraceBinary

namespace PrimitiveAffineProfile
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem complementTrace_abelianLength_le_twentyNine_of_degree128
    (P : PrimitiveAffineProfile G X) (hp : MulAction.IsPreprimitive G X)
    (x : X) (he : Nat.card X=128) (T : FixedTargetCompositionTrace (P.complement x))
    (hn : ¬ IsSolvable (P.complement x)) : T.envelope.abelianLength ≤ 29 := by
  have h := P.complementTrace_nonsoluble_saving_le_fullLinearOmega hp x
    (p := 2) (d := 7) (by decide) (by decide) (by norm_num [he]) T hn
  rw [CFSGPrimitiveAffineOrderTraceBinary.selected_binary_receipts.1] at h
  omega

theorem complementTrace_abelianLength_le_forty_of_degree256
    (P : PrimitiveAffineProfile G X) (hp : MulAction.IsPreprimitive G X)
    (x : X) (he : Nat.card X=256) (T : FixedTargetCompositionTrace (P.complement x)) :
    T.envelope.abelianLength ≤ 40 := by
  have h := P.complementTrace_abelianLength_le_fullLinearOmega hp x
    (p := 2) (d := 8) (by decide) (by decide) (by norm_num [he]) T
  simpa only [CFSGPrimitiveAffineOrderTraceBinary.selected_binary_receipts.2] using h

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics
