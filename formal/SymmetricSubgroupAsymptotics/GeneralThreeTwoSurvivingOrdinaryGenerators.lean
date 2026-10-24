import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightThreeImages
import SymmetricSubgroupAsymptotics.GeneralThreeTwoRowGenerators
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! The three surviving actual degree-eight complement models already
have checked ordinary row generators. Their third displayed generator is
the identity, so two ordinary generators suffice. No new coverage or
subgroup census is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoSurvivingOrdinaryGenerators

private def rowIndex : Fin 3 → Fin 15 := ![4,14,7]

private def triple (i : Fin 3) : Fin 3 → GeneralThreeTwoMatrixEncoding.Ambient :=
  GeneralThreeTwoRowGenerators.generators (rowIndex i)

private theorem triple_last (i : Fin 3) : triple i 2 = 1 := by
  fin_cases i <;> apply Units.ext <;> decide +kernel

theorem models_eq_closure (i : Fin 3) :
    PrimitiveAffineDegreeEightThreeImages.models i =
      Subgroup.closure (Set.range (triple i)) := by
  fin_cases i
  all_goals exact GeneralThreeTwoRowGenerators.rows_eq_closure _

/-- Removing a displayed identity from a three-generator word
presentation gives a literal finite set of at most two generators. -/
theorem closure_triple_genRank_le_two {G : Type} [Group G]
    (g : Fin 3 → G) (hthird : g 2 = 1) :
    MarkedC4.genRank (Subgroup.closure (Set.range g)) ≤ 2 := by
  let original := closureGenerators g
  let pair : Fin 2 → Subgroup.closure (Set.range g) := fun j => original j.castSucc
  let S := Subgroup.closure (Set.range pair)
  have hpair (j : Fin 2) : pair j ∈ S := Subgroup.subset_closure ⟨j,rfl⟩
  have hlast : original 2 = 1 := Subtype.ext hthird
  have hall : Subgroup.closure (Set.range original) ≤ S := by
    apply (Subgroup.closure_le S).mpr
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · exact hpair 0
    · exact hpair 1
    · change original 2 ∈ S
      rw [hlast]
      exact S.one_mem
  have hS : S = ⊤ := by
    rw [closureGenerators_full g] at hall
    exact top_le_iff.mp hall
  let s : Finset (Subgroup.closure (Set.range g)) := Finset.univ.image pair
  have hset : (s : Set (Subgroup.closure (Set.range g))) = Set.range pair := by
    simp only [s,Finset.coe_image,Finset.coe_univ,Set.image_univ]
  have hgen : Subgroup.closure (s : Set (Subgroup.closure (Set.range g))) = ⊤ := by
    rw [hset]
    exact hS
  exact (MarkedC4.genRank_le hgen).trans
    (Finset.card_image_le.trans (by simp))

theorem models_genRank_le_two (i : Fin 3) :
    MarkedC4.genRank (PrimitiveAffineDegreeEightThreeImages.models i) ≤ 2 := by
  rw [models_eq_closure i]
  exact closure_triple_genRank_le_two (triple i) (triple_last i)

end SymmetricSubgroupAsymptotics.GeneralThreeTwoSurvivingOrdinaryGenerators
