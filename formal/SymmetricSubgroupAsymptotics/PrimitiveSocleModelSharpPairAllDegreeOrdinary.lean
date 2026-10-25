import SymmetricSubgroupAsymptotics.PrimitiveSocleModelPairOrdinaryTail
import SymmetricSubgroupAsymptotics.SmallSharpOuterPairNumerics

/-! A literal generating pair and sharp outer-order bound pay every degree.
Small degrees use the actual integral outer prime multiplicity; no action
catalogue, exceptional-family callback or generator conjecture is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleModelSharpPairAllDegreeOrdinary
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) {M : Type} [Group M]

theorem genRank_le_ceiling (hk : D.factorCount=1) (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S:Set M)=⊤ ∧ S.card≤2)
    (hsharp : ∀ ell : ℕ, LeastProperIndex M ell →
      (Nat.card (Outer M):ℝ)≤3*Real.logb 2 ell) :
    MarkedC4.genRank G≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  classical
  by_cases hn : 32≤Nat.card X
  · exact PrimitiveSocleModelPairOrdinaryTail.genRank_le_ceiling D hk e hpair hsharp hn
  obtain ⟨S,hS,hcard⟩ := hpair
  let U := S.image e.symm
  have hU : Subgroup.closure (U:Set D.Simple)=⊤ := by
    rw [Finset.coe_image]
    change Subgroup.closure (e.symm.toMonoidHom '' (S:Set M))=⊤
    rw [← MonoidHom.map_closure,hS]
    exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hUcard : U.card≤2 := Finset.card_image_le.trans hcard
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hell5 : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have helln := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have hn5 : 5≤Nat.card X := hell5.trans helln
  have hout : (Nat.card (Outer D.Simple):ℝ)≤3*Real.logb 2 (Nat.card X:ℝ) := by
    rw [CFSGReduction.outer_card_congr e]
    have hs := hsharp ell (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
    have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by exact_mod_cast (show 0<ell by omega) : (0:ℝ)<ell)
      (by exact_mod_cast helln : (ell:ℝ)≤Nat.card X)
    linarith
  have hsmall := SmallSharpOuterPairNumerics.sharp_outer_small_multiplicity
    (Nat.card X) (Nat.card (Outer D.Simple)) hn5 (by omega)
    (Nat.card_pos (α:=Outer D.Simple)) hout
  have hsimple : MarkedC4.genRank D.Simple≤2 :=
    (MarkedC4.genRank_le hU).trans hUcard
  exact (PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk).trans
    ((Nat.add_le_add_right hsimple _).trans hsmall)

theorem exists_generating_finset (hk : D.factorCount=1) (e : D.Simple ≃* M)
    (hpair : ∃ S : Finset M, Subgroup.closure (S:Set M)=⊤ ∧ S.card≤2)
    (hsharp : ∀ ell : ℕ, LeastProperIndex M ell →
      (Nat.card (Outer M):ℝ)≤3*Real.logb 2 ell) :
    ∃ U : Finset G, Subgroup.closure (U:Set G)=⊤ ∧
      U.card≤traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U,hU,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨U,hgen,hU.le.trans (genRank_le_ceiling D hk e hpair hsharp)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleModelSharpPairAllDegreeOrdinary
