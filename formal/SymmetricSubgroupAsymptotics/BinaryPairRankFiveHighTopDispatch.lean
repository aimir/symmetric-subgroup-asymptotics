import SymmetricSubgroupAsymptotics.BinaryEightHighTopReduction

/-! The residual rank-five pair frame is either covered by the generic
small-top route or reindexed to one of three actual large tops. The source
U and every original normal subgroup are unchanged by this point chart. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 8))

theorem rank_five_residual_high_top_dispatch
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hregular : ¬ ∃ c : Equiv.Perm (Fin 8), MulAut.conj c • F.top.range =
      Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hheisenberg : ¬ ∃ c : Equiv.Perm (Fin 8), MulAut.conj c • F.top.range =
      Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)) :
    Nat.card F.top.range ≤ 32 ∨ ∃ c : Equiv.Perm (Fin 8),
      (F.reindex c).top.range = Subgroup.closure (Set.range BinaryMenuCayley8T29.generators) ∨
      (F.reindex c).top.range = Subgroup.closure (Set.range BinaryMenuCayley8T30.generators) ∨
      (F.reindex c).top.range = Subgroup.closure (Set.range BinaryMenuCayley8T31.generators) := by
  by_cases hsmall : Nat.card F.top.range ≤ 32
  · exact Or.inl hsmall
  letI residualHigh_topPretransitive : MulAction.IsPretransitive F.top.range (Fin 8) :=
    F.top_pretransitive
  letI residualHigh_pairAction : MulAction U (Fin 8) := MulAction.compHom (Fin 8) F.top
  letI residualHigh_pairPretransitive : MulAction.IsPretransitive U (Fin 8) := ⟨by
    intro i j
    obtain ⟨t,ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨u,ht⟩⟩
  have hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i := fun _ _ => rfl
  obtain ⟨_,_,htop,_,_,_⟩ :=
    F.rank_five_residual_top_saturation hact hU hrank hregular hheisenberg
  have htrans : ∀ i j : Fin 8, ∃ t : F.top.range, t.val i = j := by
    intro i j
    exact MulAction.exists_smul_eq F.top.range i j
  obtain ⟨c,hc⟩ := BinaryEightHighTopReduction.large_top_cover F.top.range
    (F.top_isPGroup hU) htrans (by omega) (by omega)
    (F.no_top_singlePowerOrbit_of_rank_five hact hU hrank (by omega))
  refine Or.inr ⟨c,?_⟩
  rw [F.reindex_top_range_conjugation]
  exact hc

end SymmetricSubgroupAsymptotics.BinaryPairFrame
