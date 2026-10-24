import SymmetricSubgroupAsymptotics.GeneralThreeTwoSmallAffineBindings
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSurvivingOrdinaryGenerators
import SymmetricSubgroupAsymptotics.GeneralThreeTwoTwentyOneSinger
import SymmetricSubgroupAsymptotics.SmallAffineTwentyOneSelfCentralizingSeven
import SymmetricSubgroupAsymptotics.ProjectiveThreeSimplicity
import SymmetricSubgroupAsymptotics.MetacyclicNormalGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Lean.Elab.Tactic.Omega

/-! Actual subnormal-image facts for the three already checked
degree-eight complement models. Prime order, unconditional GL3(2)
simplicity, and the actual normal self-centralizing C7 are used; no new
subgroup census or published classification hypothesis is introduced. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoSurvivingSubnormal
open PrimitiveAffineDegreeEightThreeImages GeneralThreeTwoSmallAffineBindings

theorem model_zero_card : Nat.card (models 0) = 7 :=
  (Nat.card_congr sevenEquiv.toEquiv).trans SmallAffineSoluble8Row1Order.card

theorem model_two_simple : IsSimpleGroup (models 2) := by
  letI : IsSimpleGroup (StandardThreeDimensionalLinearGroups.GeneralThree 2) :=
    StandardThreeDimensionalLinearGroups.simple_GL_two ProjectiveThreeSimplicity.proved
  exact fullEquiv.isSimpleGroup

def model_one_singer : models 1 :=
  ⟨GeneralThreeTwoTwentyOneSinger.singer,by
    change GeneralThreeTwoRowGenerators.generators 14 0 ∈
      GeneralThreeTwoActualSubgroupCoverage.rows 14
    rw [GeneralThreeTwoRowGenerators.rows_eq_closure]
    exact Subgroup.subset_closure ⟨0,rfl⟩⟩

theorem model_one_singer_image :
    twentyOneEquiv model_one_singer =
      SmallAffineTwentyOneSelfCentralizingSeven.singer ^ 2 := by
  apply Subtype.ext
  change (MulAut.conj (GeneralThreeTwoPointAction.action twentyOneConjugator))
    (GeneralThreeTwoPointAction.action (GeneralThreeTwoRowGenerators.generators 14 0)) =
      SmallAffineSoluble8Row2Order.g0 ^ 2
  rw [pow_two]
  have hh := twentyOneCertificate.forward.equations (0 : Fin 3)
  change SmallAffineSoluble8Row2Order.g0 * SmallAffineSoluble8Row2Order.g0 =
    (MulAut.conj (GeneralThreeTwoPointAction.action twentyOneConjugator))
      (GeneralThreeTwoPointAction.action (GeneralThreeTwoRowGenerators.generators 14 0)) at hh
  exact hh.symm

theorem model_one_subnormal_contains_singer
    (N : Subgroup (models 1)) (hN : N.IsSubnormal) (hne : N ≠ ⊥) :
    model_one_singer ∈ N := by
  let M := N.map twentyOneEquiv.toMonoidHom
  have hM : M.IsSubnormal := hN.map twentyOneEquiv.surjective
  have hMne : M ≠ ⊥ := by
    intro he
    exact hne ((N.map_eq_bot_iff_of_injective twentyOneEquiv.injective).mp he)
  have hseven := SmallAffineTwentyOneSelfCentralizingSeven.seven_le_of_nontrivial_subnormal
    M hM hMne
  have hs : twentyOneEquiv model_one_singer ∈ M := by
    rw [model_one_singer_image]
    exact hseven (SmallAffineTwentyOneSelfCentralizingSeven.seven.pow_mem
      (Subgroup.mem_zpowers SmallAffineTwentyOneSelfCentralizingSeven.singer) 2)
  obtain ⟨n,hn,he⟩ := hs
  have he' : n = model_one_singer := twentyOneEquiv.injective he
  simpa only [he'] using hn

private theorem twentyOne_subgroup_genRank_le_two
    (N : Subgroup SmallAffineSoluble8Row2Order.R) : MarkedC4.genRank N ≤ 2 := by
  let P := SmallAffineTwentyOneSelfCentralizingSeven.seven
  letI : P.Normal := SmallAffineTwentyOneSelfCentralizingSeven.seven_normal
  have hindex : P.index = 3 := by
    have h := P.card_mul_index
    rw [SmallAffineTwentyOneSelfCentralizingSeven.seven_card,
      SmallAffineSoluble8Row2Order.card] at h
    omega
  have hquot : Nat.card (SmallAffineSoluble8Row2Order.R ⧸ P) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hindex
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : IsCyclic (SmallAffineSoluble8Row2Order.R ⧸ P) := isCyclic_of_prime_card hquot
  let f := QuotientGroup.mk' P
  have hker : f.ker = P := QuotientGroup.ker_mk' P
  letI : IsCyclic f.ker := by
    rw [hker]
    change IsCyclic (Subgroup.zpowers SmallAffineTwentyOneSelfCentralizingSeven.singer)
    infer_instance
  exact MarkedC4.genRank_subgroup_le_two_of_cyclic_kernel f N

private theorem model_zero_subgroup_rank (N : Subgroup (models 0)) :
    MarkedC4.genRank N ≤ 2 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : IsCyclic (models 0) := isCyclic_of_prime_card model_zero_card
  letI : IsCyclic N := isCyclic_of_injective N.subtype N.subtype_injective
  exact MarkedC4.genRank_le_one_of_isCyclic.trans (by decide)

private theorem model_two_subnormal_rank (N : Subgroup (models 2))
    (hN : N.IsSubnormal) : MarkedC4.genRank N ≤ 2 := by
  rcases hN.eq_bot_or_top_of_isSimpleGroup model_two_simple with hzero | hfull
  · rw [hzero]
    letI : Unique (⊥ : Subgroup (models 2)) := {
      default := 1
      uniq := fun x => Subtype.ext (Subgroup.mem_bot.mp x.property) }
    have hcard : Nat.card (⊥ : Subgroup (models 2)) = 1 := Nat.card_unique
    exact FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow
      (⊥ : Subgroup (models 2)) 2 (hcard.le.trans (by decide))
  · rw [hfull]
    exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (Subgroup.topEquiv : (⊤ : Subgroup (models 2)) ≃* models 2)).le.trans
        (GeneralThreeTwoSurvivingOrdinaryGenerators.models_genRank_le_two 2)

theorem model_subnormal_genRank_le_two (i : Fin 3) (N : Subgroup (models i))
    (hN : N.IsSubnormal) : MarkedC4.genRank N ≤ 2 := by
  fin_cases i
  · exact model_zero_subgroup_rank N
  · let e := N.equivMapOfInjective twentyOneEquiv.toMonoidHom twentyOneEquiv.injective
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
    exact twentyOne_subgroup_genRank_le_two _
  · exact model_two_subnormal_rank N hN

end SymmetricSubgroupAsymptotics.GeneralThreeTwoSurvivingSubnormal
