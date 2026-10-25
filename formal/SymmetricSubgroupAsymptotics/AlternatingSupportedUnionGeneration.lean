import SymmetricSubgroupAsymptotics.AlternatingSupportedOverlapGeneration

/-! Supported alternating subgroups glue on their literal union when
their supports share two points. The union is used as an actual subtype
of the original carrier, and every generating cycle is extended by the
identity. No transitive-action or small-index recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingSupportedUnionGeneration
open Equiv Equiv.Perm CFSGAlternatingStarGenerators CFSGAlternatingThreeCycleStars

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem supported_mono (S T : Finset X) (hST : S ⊆ T) :
    (alternatingGroup.ofSubtype S).range ≤ (alternatingGroup.ofSubtype T).range := by
  intro g hg
  apply (alternatingGroup.mem_range_ofSubtype_iff T g).mpr
  exact ((alternatingGroup.mem_range_ofSubtype_iff S g).mp hg).trans hST

theorem union_le_of_common_pair
    (H : Subgroup (alternatingGroup X)) (S T : Finset X)
    (a b : X) (hab : a ≠ b)
    (haS : a ∈ S) (hbS : b ∈ S) (haT : a ∈ T) (hbT : b ∈ T)
    (hS : (alternatingGroup.ofSubtype S).range ≤ H)
    (hT : (alternatingGroup.ofSubtype T).range ≤ H) :
    (alternatingGroup.ofSubtype (S ∪ T)).range ≤ H := by
  let U := S ∪ T
  let f : alternatingGroup U →* alternatingGroup X := alternatingGroup.ofSubtype U
  let L : Subgroup (alternatingGroup U) := H.comap f
  let K : Subgroup (Perm U) := L.map (alternatingGroup U).subtype
  let aU : U := ⟨a, Finset.mem_union.mpr (Or.inl haS)⟩
  let bU : U := ⟨b, Finset.mem_union.mpr (Or.inl hbS)⟩
  have habU : aU ≠ bU := fun h => hab (congrArg Subtype.val h)
  have hfull : alternatingGroup U ≤ K := by
    apply alternating_le_of_star K aU bU habU
    intro c hca hcb
    have hca' : c.val ≠ a := fun h => hca (Subtype.ext h)
    have hcb' : c.val ≠ b := fun h => hcb (Subtype.ext h)
    have heven : cycle aU bU c ∈ alternatingGroup U :=
      (cycle_isThreeCycle aU bU c habU (Ne.symm hca) (Ne.symm hcb)).mem_alternatingGroup
    let u : alternatingGroup U := ⟨cycle aU bU c, heven⟩
    have he : ((f u : alternatingGroup X) : Perm X) = cycle a b c.val := by
      change Perm.ofSubtype (cycle aU bU c) = cycle a b c.val
      simp only [cycle, map_mul, Perm.ofSubtype_swap_eq]
      rfl
    have hfu : f u ∈ H := by
      have supported_mem (s : Finset X)
          (hs : (alternatingGroup.ofSubtype s).range ≤ H)
          (ha : a ∈ s) (hb : b ∈ s) (hc : c.val ∈ s) : f u ∈ H := by
        apply hs
        apply (alternatingGroup.mem_range_ofSubtype_iff s (f u)).mpr
        rw [he, cycle_support a b c.val hab (Ne.symm hca') (Ne.symm hcb')]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨ha, hb, hc⟩
      rcases Finset.mem_union.mp c.property with hcS | hcT
      · exact supported_mem S hS haS hbS hcS
      · exact supported_mem T hT haT hbT hcT
    exact Subgroup.mem_map.mpr ⟨u, hfu, rfl⟩
  rintro g ⟨u, rfl⟩
  have hu : (u : Perm U) ∈ K := hfull u.property
  obtain ⟨v, hv, he⟩ := Subgroup.mem_map.mp hu
  have hvu : v = u := Subtype.ext he
  exact hvu ▸ hv

theorem join_eq_union_of_two_le_inter_card (S T : Finset X)
    (hinter : 2 ≤ (S ∩ T).card) :
    (alternatingGroup.ofSubtype S).range ⊔ (alternatingGroup.ofSubtype T).range =
      (alternatingGroup.ofSubtype (S ∪ T)).range := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (S ∩ T).card)
  apply le_antisymm
  · exact sup_le
      (supported_mono S (S ∪ T) Finset.subset_union_left)
      (supported_mono T (S ∪ T) Finset.subset_union_right)
  · exact union_le_of_common_pair _ S T a b hab
      (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1
      (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2 le_sup_left le_sup_right

end SymmetricSubgroupAsymptotics.AlternatingSupportedUnionGeneration
