import SymmetricSubgroupAsymptotics.MarkedC4RDTExcessStructure
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! The excess-one generator-rank hypothesis in ordinary RDT5.7 is
DERIVED from an actual excessive quotient normal subgroup and the ordinary
RDT5.3 assertion that only the original whole group is excessive. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualExcessOneQuotientRank
open RDTExcessStructure

theorem normalGen_top_le_genRank (G : Type) [Group G] [Finite G] :
    normalGen (⊤ : Subgroup G)≤genRank G := by
  obtain ⟨S,hS,hgen⟩ := genRank_spec (G := G)
  have hcl : Subgroup.normalClosure (S : Set G)=⊤ := by
    apply top_unique
    rw [← hgen]
    exact Subgroup.closure_le_normalClosure
  exact (normalGen_le (N := (⊤ : Subgroup G)) (s := S) (by intro x hx; trivial) hcl).trans_eq hS

theorem normalGen_top_eq_genRank (G : Type) [Group G] [Finite G] [Group.IsNilpotent G] :
    normalGen (⊤ : Subgroup G)=genRank G :=
  le_antisymm (normalGen_top_le_genRank G) (genRank_le_normalGen_top (G := G))

theorem quotient_rank_eq {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    [Group.IsNilpotent G] (q : G →* Q) (hq : Function.Surjective q)
    (n : ℕ) (hexcess : HasExcess G n 1)
    (honly : ∀ U : Subgroup G,U.Normal →(n : ℝ)/4<(normalGen U : ℝ) →U=⊤)
    (V : Subgroup Q) [V.Normal] (hV : (n : ℝ)/4<(normalGen V : ℝ)) :
    genRank Q=genRank G := by
  letI : Group.IsNilpotent Q := Group.nilpotent_of_surjective q hq
  have hmap : (V.comap q).map q=V := by
    apply Subgroup.map_comap_eq_self
    rw [q.range_eq_top_of_surjective hq]
    exact le_top
  have hnormal : normalGen V≤normalGen (V.comap q) := by
    have h := normalGen_map_le q hq (V.comap q)
    rw [hmap] at h
    exact h
  have hreal : (normalGen V : ℝ)≤normalGen (V.comap q) := by exact_mod_cast hnormal
  have hpre : V.comap q=⊤ := honly _ inferInstance (lt_of_lt_of_le hV hreal)
  have hVtop : V=⊤ := by
    rw [← hmap,hpre]
    exact Subgroup.map_top_of_surjective q hq
  obtain ⟨U,hUn,hU⟩ := hexcess.1
  have hUtop : U=⊤ := honly U hUn (by push_cast at hU; linarith)
  rw [hUtop,normalGen_top_eq_genRank G] at hU
  rw [hVtop,normalGen_top_eq_genRank Q] at hV
  have hupper := ActualGlobalMarkGeneratorRank.genRank_le_of_surjective q hq
  have hlt : (genRank G : ℝ)<(genRank Q : ℝ)+1 := by push_cast at hU; linarith
  have hnat : genRank G<genRank Q+1 := by exact_mod_cast hlt
  omega

end SymmetricSubgroupAsymptotics.MarkedC4.ActualExcessOneQuotientRank
