import SymmetricSubgroupAsymptotics.CFSGPSLTwoProductTorusCover

/-! Solubility of the actual Borel-power image used in the correlated
cover geometry. The same derived-series length works in every coordinate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBorelSolvable

theorem function_group_isSolvable {G J : Type*} [Group G] [IsSolvable G] :
    IsSolvable (J → G) := by
  obtain ⟨n,hn⟩ := IsSolvable.solvable (G:=G)
  refine ⟨⟨n,bot_unique ?_⟩⟩
  intro g hg
  apply Subgroup.mem_bot.mpr
  funext i
  let ev : (J → G) →* G :=
    { toFun := fun h => h i
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hh : ev g ∈ derivedSeries G n :=
    map_derivedSeries_le_derivedSeries ev n ⟨g,hg,rfl⟩
  rw [hn] at hh
  exact Subgroup.mem_bot.mp hh

open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoProductTorusCover
variable {F J : Type*} [Field F]

theorem projectiveBorel_isSolvable : IsSolvable (projectiveBorel (F:=F)) := by
  letI := CFSGSLTwoUpperRoots.borel_isSolvable (F:=F)
  let f := (projection (F:=F)).subgroupMap (CFSGSLTwoUpperRoots.borel (F:=F))
  exact solvable_of_surjective (f:=f)
    ((projection (F:=F)).subgroupMap_surjective (CFSGSLTwoUpperRoots.borel (F:=F)))

theorem borelPower_isSolvable : IsSolvable (J → projectiveBorel (F:=F)) := by
  letI := projectiveBorel_isSolvable (F:=F)
  exact function_group_isSolvable

theorem actual_borelPower_image_isSolvable :
    IsSolvable (borelPowerHom (F:=F) (J:=J)).range := by
  letI := borelPower_isSolvable (F:=F) (J:=J)
  exact solvable_of_surjective (f:=(borelPowerHom (F:=F) (J:=J)).rangeRestrict)
    (borelPowerHom (F:=F) (J:=J)).rangeRestrict_surjective

end SymmetricSubgroupAsymptotics.CFSGPSLTwoProductBorelSolvable
