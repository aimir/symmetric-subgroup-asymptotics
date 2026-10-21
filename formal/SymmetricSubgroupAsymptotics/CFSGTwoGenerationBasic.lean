import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Finset.Card

/-! Elementary two-generation tools, retaining actual generating subsets.
No finiteness, simplicity, or classification assumption is used here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGeneration
universe u v

abbrev TwoGenerated (G : Type u) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ 2

variable {G : Type u} [Group G]

theorem of_generating_family {ι : Type v} [Finite ι]
    (a : ι → G) (ha : Subgroup.closure (Set.range a) = ⊤)
    (hcard : Nat.card ι ≤ 2) : TwoGenerated G := by
  letI twoGenerationBasic_fintype : Fintype ι := Fintype.ofFinite ι
  let S : Finset G := Finset.univ.image a
  have hs : (S : Set G) = Set.range a := by
    ext x
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine ⟨S, ?_, ?_⟩
  · rw [hs]
    exact ha
  · exact Finset.card_image_le.trans (by
      simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hcard)

theorem of_surjective {H : Type v} [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hG : TwoGenerated G) : TwoGenerated H := by
  obtain ⟨S, hS, hcard⟩ := hG
  refine ⟨S.image f, ?_, Finset.card_image_le.trans hcard⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hS]
  exact Subgroup.map_top_of_surjective f hf

theorem of_mulEquiv {H : Type v} [Group H] (e : G ≃* H)
    (hG : TwoGenerated G) : TwoGenerated H :=
  of_surjective e.toMonoidHom e.surjective hG

theorem closure_of_family {ι : Type v} [Finite ι]
    (a : ι → G) (hcard : Nat.card ι ≤ 2) : TwoGenerated (Subgroup.closure (Set.range a)) :=
  of_generating_family (closureGenerators a) (closureGenerators_full a) hcard

/-- Two fibres of an injective ambient map contain at most two actual
original generators. Neither fibre is assumed nonempty. -/
theorem closure_of_two_fibres {A : Type v}
    (s : Set G) (f : G → A) (hf : Function.Injective f) (a b : A)
    (hs : ∀ g ∈ s, f g = a ∨ f g = b) : TwoGenerated (Subgroup.closure s) := by
  let label : s → Fin 2 := fun g => if f g.val = a then 0 else 1
  have hlabel : Function.Injective label := by
    intro x y he
    apply Subtype.ext
    apply hf
    by_cases hx : f x.val = a
    · by_cases hy : f y.val = a
      · exact hx.trans hy.symm
      · have hbad : (0 : Fin 2) = 1 := by simpa only [label, if_pos hx, if_neg hy] using he
        exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hbad)
    · by_cases hy : f y.val = a
      · have hbad : (1 : Fin 2) = 0 := by simpa only [label, if_neg hx, if_pos hy] using he
        exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hbad)
      · exact ((hs x.val x.property).resolve_left hx).trans
          ((hs y.val y.property).resolve_left hy).symm
  letI twoGenerationBasic_finiteGenerators : Finite s := Finite.of_injective label hlabel
  have hcard : Nat.card s ≤ 2 := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective label hlabel
  let k : s → G := Subtype.val
  have hk : Set.range k = s := Subtype.range_coe
  exact of_mulEquiv (MulEquiv.subgroupCongr (congrArg Subgroup.closure hk))
    (closure_of_family k hcard)

theorem closure_pair (a b : G) : TwoGenerated (Subgroup.closure ({a, b} : Set G)) := by
  apply closure_of_two_fibres ({a, b} : Set G) id Function.injective_id a b
  intro g hg
  simpa only [id_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using hg

theorem presented_on_two_generators (rels : Set (FreeGroup (Fin 2))) :
    TwoGenerated (PresentedGroup rels) :=
  of_generating_family PresentedGroup.of (PresentedGroup.closure_range_of rels) (by simp)

end SymmetricSubgroupAsymptotics.CFSGGeneration
