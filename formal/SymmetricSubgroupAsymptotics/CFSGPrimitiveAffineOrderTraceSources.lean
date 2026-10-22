import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceMargins

/-! Actual original-normal affine owner sources at49/128/256 from order
prime-factor budgets. No primitive composition-length premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.CFSGPrimitiveAffineOrderTraceSources

noncomputable def source49
    (U : PreE7NonPairActionClass 49)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 49 U) (Fin 49))
    (P : PrimitiveAffineProfile (preE7NonPairAction 49 U) (Fin 49))
    (hn : ¬ IsSolvable (P.complement ⟨0,by decide⟩)) :
    PreE7RankTailOwnerSourceData 49 U := by
  let x : Fin 49 := ⟨0,by decide⟩
  let C := P.elementaryChart hp
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by decide) (by decide) hp P x C T hn
    (P.nonsoluble_margin_of_degree49_order hp x (by simp) T)

noncomputable def source128
    (U : PreE7NonPairActionClass 128)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 128 U) (Fin 128))
    (P : PrimitiveAffineProfile (preE7NonPairAction 128 U) (Fin 128))
    (hn : ¬ IsSolvable (P.complement ⟨0,by decide⟩)) :
    PreE7RankTailOwnerSourceData 128 U := by
  let x : Fin 128 := ⟨0,by decide⟩
  let C := P.elementaryChart hp
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by decide) (by decide) hp P x C T hn
    (P.nonsoluble_margin_of_degree128_order hp x (by simp) T hn)

noncomputable def source256
    (U : PreE7NonPairActionClass 256)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction 256 U) (Fin 256))
    (P : PrimitiveAffineProfile (preE7NonPairAction 256 U) (Fin 256))
    (hn : ¬ IsSolvable (P.complement ⟨0,by decide⟩)) :
    PreE7RankTailOwnerSourceData 256 U := by
  let x : Fin 256 := ⟨0,by decide⟩
  let C := P.elementaryChart hp
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by decide) (by decide) hp P x C T hn
    (P.nonsoluble_margin_of_degree256_order hp x (by simp) T)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.CFSGPrimitiveAffineOrderTraceSources
