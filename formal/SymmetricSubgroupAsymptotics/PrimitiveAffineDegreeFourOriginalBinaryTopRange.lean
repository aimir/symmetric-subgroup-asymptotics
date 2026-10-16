import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinaryTopInjection
import SymmetricSubgroupAsymptotics.OriginalRetainedTopQuotientEvaluation

/-! Actual normal binary image of the named top injection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]
local instance originalBinaryTopRangePrime : Fact P.p.Prime := ⟨P.p_prime⟩

theorem degreeFourFullBinaryTopInjection_range
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (degreeFourFullBinaryTopInjection block P N).range =
      (DegreeFourFullBinarySocle block P N).map
        (QuotientGroup.mk' (degreeFourTranslationImage block P N)) := by
  let C := DegreeFourFullBinarySocleChart block P N
  let T := DegreeFourFullBinaryTargetSection block P N
  let q := QuotientGroup.mk' (degreeFourTranslationImage block P N)
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    obtain ⟨x,hx⟩ := T.toSubmodule.mkQ_surjective v.toAdd
    have hv : Multiplicative.ofAdd (T.toSubmodule.mkQ x) = v := congrArg Multiplicative.ofAdd hx
    rw [← hv]
    dsimp only [T]
    have heval := degreeFourFullBinaryTopInjection_mk
      (block := block) (P := P) (N := N) (v := x)
    have hm : q ((C.equiv.symm (Multiplicative.ofAdd x)).1) ∈
        (DegreeFourFullBinarySocle block P N).map q :=
      ⟨(C.equiv.symm (Multiplicative.ofAdd x)).1,
        (C.equiv.symm (Multiplicative.ofAdd x)).2,rfl⟩
    exact heval.symm ▸ hm
  · rintro _ ⟨a,ha,rfl⟩
    let v := (C.equiv ⟨a,ha⟩).toAdd
    refine ⟨Multiplicative.ofAdd (T.toSubmodule.mkQ v),?_⟩
    have heval := degreeFourFullBinaryTopInjection_mk
      (block := block) (P := P) (N := N) (v := v)
    have hev : C.equiv.symm (Multiplicative.ofAdd v) = ⟨a,ha⟩ :=
      C.equiv.symm_apply_apply ⟨a,ha⟩
    exact heval.trans (congrArg (fun z : DegreeFourFullBinarySocle block P N => q z.1) hev)

instance degreeFourFullBinaryTopInjection_range_normal
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (degreeFourFullBinaryTopInjection block P N).range.Normal := by
  rw [degreeFourFullBinaryTopInjection_range]
  exact Subgroup.Normal.map inferInstance _
    (QuotientGroup.mk'_surjective (degreeFourTranslationImage block P N))

theorem degreeFourFullBinaryTopInjection_range_isPGroup
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    IsPGroup 2 (degreeFourFullBinaryTopInjection block P N).range := by
  rw [degreeFourFullBinaryTopInjection_range]
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  have h : IsPGroup P.p (DegreeFourFullBinarySocle block P N) :=
    primePrimarySoclePart_isPGroup_of_predicate P.p
      (DegreeFourRetainedQuotient N) (degreeFourFullBinarySelector N)
  rw [hp] at h
  exact h.map (QuotientGroup.mk' (degreeFourTranslationImage block P N))

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
