import SymmetricSubgroupAsymptotics.CFSGFiniteFamilyGeneration

/-! Actual generation information for the pinned three-generator J4
presentation. The unconditional bound here is three, not two. The pair
`(x*t,y)` normally generates the model, which does not establish that it
generates the model as an ordinary subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGeneration

theorem presented_generators_card_le {ι : Type*} [Finite ι]
    (rels : Set (FreeGroup ι)) :
    ∃ S : Finset (PresentedGroup rels),
      Subgroup.closure (S : Set (PresentedGroup rels)) = ⊤ ∧ S.card ≤ Nat.card ι := by
  letI cfsgPresentedGenerators_fintype : Fintype ι := Fintype.ofFinite ι
  let S : Finset (PresentedGroup rels) := Finset.univ.image PresentedGroup.of
  have hS : (S : Set (PresentedGroup rels)) = Set.range PresentedGroup.of := by
    ext g
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine ⟨S, ?_, ?_⟩
  · rw [hS]
    exact PresentedGroup.closure_range_of rels
  · exact Finset.card_image_le.trans (by
      simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
        (le_rfl : Fintype.card ι ≤ Fintype.card ι))

theorem j4_three_generators :
    ∃ S : Finset CFSG.Models.Presentations.J4.Model,
      Subgroup.closure (S : Set CFSG.Models.Presentations.J4.Model) = ⊤ ∧
      S.card ≤ 3 := by
  simpa only [Nat.card_fin] using
    (presented_generators_card_le {w | w ∈ CFSG.Models.Presentations.J4.relators})

theorem j4_aut_card_le_cube [Finite CFSG.Models.Presentations.J4.Model] :
    Nat.card (CFSG.Models.Presentations.J4.Model ≃* CFSG.Models.Presentations.J4.Model) ≤
      Nat.card CFSG.Models.Presentations.J4.Model ^ 3 := by
  obtain ⟨S, hS, hcard⟩ := j4_three_generators
  exact aut_card_le_pow_of_generators S hS hcard

abbrev j4x : CFSG.Models.Presentations.J4.Model := PresentedGroup.of (0 : Fin 3)
abbrev j4y : CFSG.Models.Presentations.J4.Model := PresentedGroup.of (1 : Fin 3)
abbrev j4t : CFSG.Models.Presentations.J4.Model := PresentedGroup.of (2 : Fin 3)

theorem j4x_sq : j4x ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ CFSG.Models.Presentations.J4.relators})
    (x := (FreeGroup.of (0 : Fin 3)) ^ 2)
    (by change _ ∈ CFSG.Models.Presentations.J4.relators
        exact List.mem_cons_self)
  simpa only [map_pow, PresentedGroup.of] using h

theorem j4xy_pow_twenty_three : (j4x * j4y) ^ 23 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ CFSG.Models.Presentations.J4.relators})
    (x := (FreeGroup.of (0 : Fin 3) * FreeGroup.of (1 : Fin 3)) ^ 23)
    (by change _ ∈ CFSG.Models.Presentations.J4.relators
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simpa only [map_pow, map_mul, PresentedGroup.of] using h

/-- A normal subgroup containing the candidate pair must be the whole
actual presented group. This does not supply normality of its closure. -/
theorem j4_eq_top_of_normal_contains_candidate
    (N : Subgroup CFSG.Models.Presentations.J4.Model) [N.Normal]
    (ha : j4x * j4t ∈ N) (hy : j4y ∈ N) : N = ⊤ := by
  let q : CFSG.Models.Presentations.J4.Model →*
      CFSG.Models.Presentations.J4.Model ⧸ N := QuotientGroup.mk' N
  have hyq : q j4y = 1 := (QuotientGroup.eq_one_iff j4y).mpr hy
  have h2 : (q j4x) ^ 2 = 1 := by
    simpa only [map_pow, map_one] using congrArg q j4x_sq
  have h23 : (q j4x) ^ 23 = 1 := by
    simpa only [map_pow, map_mul, map_one, hyq, mul_one] using
      congrArg q j4xy_pow_twenty_three
  have h22 : (q j4x) ^ 22 = 1 := by
    rw [show 22 = 2 * 11 by decide, pow_mul, h2, one_pow]
  have hxq : q j4x = 1 := by
    simpa only [show 23 = 22 + 1 by decide, pow_add, h22, pow_one, one_mul] using h23
  have hx : j4x ∈ N := (QuotientGroup.eq_one_iff j4x).mp hxq
  have ht : j4t ∈ N := by
    simpa only [inv_mul_cancel_left] using N.mul_mem (N.inv_mem hx) ha
  apply top_unique
  intro g _
  exact PresentedGroup.generated_by _ N (fun i => by
    fin_cases i
    · exact hx
    · exact hy
    · exact ht) g

theorem j4_candidate_normally_generates :
    Subgroup.normalClosure ({j4x * j4t, j4y} :
      Set CFSG.Models.Presentations.J4.Model) = ⊤ := by
  apply j4_eq_top_of_normal_contains_candidate
  · exact Subgroup.subset_normalClosure (by simp)
  · exact Subgroup.subset_normalClosure (by simp)

end SymmetricSubgroupAsymptotics.CFSGGeneration
